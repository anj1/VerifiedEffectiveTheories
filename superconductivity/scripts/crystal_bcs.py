#!/usr/bin/env python3
"""Predict and certify finite-band static BCS observables from a periodic site model."""
import argparse
from dataclasses import dataclass
from fractions import Fraction
import json
from math import ceil, factorial, isqrt
from pathlib import Path

from pairing import crossing, lean_rat, lean_vec, rational

TERMS = 16
EXPANSION_LIMIT = 32


@dataclass(frozen=True)
class Crystal:
    hopping: tuple
    stiffness: Fraction
    deformation: Fraction
    repulsion: Fraction
    chemical_potential: Fraction

    @property
    def induced(self):
        return self.deformation**2 / self.stiffness

    @property
    def xi(self):
        return tuple(
            sum((-1)**((a & i).bit_count()) * value for a, value in enumerate(self.hopping))
            - self.induced / 2 - self.chemical_potential
            for i in range(len(self.hopping))
        )

    @property
    def coupling(self):
        # Each normalized orbital has site probability 1/N.
        return (self.induced - self.repulsion) / len(self.hopping)


def read_crystal(path, *, require_separated_levels=True):
    raw = json.loads(path.read_text(), parse_float=Fraction)
    if not isinstance(raw["hopping_by_displacement_mev"], list):
        raise ValueError("hopping_by_displacement_mev must be an array")
    crystal = Crystal(
        tuple(map(rational, raw["hopping_by_displacement_mev"])),
        rational(raw["stiffness_mev_per_angstrom2"]),
        rational(raw["deformation_mev_per_angstrom"]),
        rational(raw["screened_onsite_repulsion_mev"]),
        rational(raw["chemical_potential_mev"]),
    )
    n = len(crystal.hopping)
    if not n or n & (n - 1):
        raise ValueError("the periodic displacement array must have power-of-two length")
    if crystal.stiffness <= 0 or crystal.repulsion < 0:
        raise ValueError("need positive stiffness and nonnegative screened onsite repulsion")
    if require_separated_levels and 0 in crystal.xi:
        raise ValueError("the finite-band certificate requires nonzero distances from the chemical potential")
    return crystal


@dataclass(frozen=True)
class Response:
    lo: Fraction
    hi: Fraction
    witness: tuple

    @property
    def side(self):
        if self.lo > 1:
            return "above_one"
        if self.hi < 1:
            return "below_one"
        return "unresolved"


def fermi_bounds(exponent, scale):
    if exponent > EXPANSION_LIMIT:
        # At low temperatures the ratio is close to one. Bound it without
        # constructing an enormous rational exponential.
        series = sum(exponent**k / factorial(k) for k in range(TERMS))
        at_limit = sum(Fraction(1, factorial(k)) for k in range(TERMS))**EXPANSION_LIMIT
        lower = max(series, at_limit)
        return (lower - 1) / (lower + 1), Fraction(1)
    y = exponent / scale
    polynomial = sum(y**k / factorial(k) for k in range(TERMS))
    tail = y**TERMS * Fraction(TERMS + 1, factorial(TERMS) * TERMS)
    lower, upper = polynomial**scale, (polynomial + tail)**scale
    return (lower - 1) / (lower + 1), (upper - 1) / (upper + 1)


def critical_bounds(xi, g, t):
    scales = tuple(max(1, ceil(min(EXPANSION_LIMIT, abs(level) / t))) for level in xi)
    values = [fermi_bounds(abs(level) / t, scale) for level, scale in zip(xi, scales)]
    return Response(*(g * sum(edge[k] / (2 * abs(level)) for edge, level in zip(values, xi))
                      for k in range(2)), scales)


def sqrt_bounds(square, grid):
    scaled = square * grid**2
    integer = isqrt(scaled.numerator // scaled.denominator)
    lower = Fraction(integer, grid)
    return lower, lower if lower**2 == square else Fraction(integer + 1, grid)


def gap_bounds(xi, g, delta, grid):
    energies = [sqrt_bounds(level**2 + delta**2, grid) for level in xi]
    lo, hi = tuple(zip(*energies))
    return Response(g * sum(1 / (2 * energy) for energy in hi),
                    g * sum(1 / (2 * energy) for energy in lo), (lo, hi))


def thermal_gap_bounds(xi, g, t, delta, grid):
    lo, hi = tuple(zip(*(sqrt_bounds(level**2 + delta**2, grid) for level in xi)))
    lower, upper = critical_bounds(hi, g, t), critical_bounds(lo, g, t)
    return Response(lower.lo, upper.hi, (lo, hi, lower.witness, upper.witness))


def automatic_bracket(response, high, tolerance):
    while response(high).side != "below_one":
        high *= 2
    cold = high / 2
    while response(cold).side != "above_one":
        cold /= 2
    return crossing(response, cold, high, tolerance)


def predict(crystal, tolerance):
    xi, g = crystal.xi, crystal.coupling
    limit = g * sum(1 / (2 * abs(level)) for level in xi)
    if limit <= 1:
        return None
    high = max(g * len(xi), max(map(abs, xi)))
    grid = ceil(10**12 / min(tolerance, 1, min(map(abs, xi)) * min(1, limit - 1)))
    critical = automatic_bracket(lambda t: critical_bounds(xi, g, t), high, tolerance)
    gap = automatic_bracket(lambda d: gap_bounds(xi, g, d, grid), high, tolerance)
    index = min(range(len(xi)), key=lambda i: abs(xi[i]))
    excitation = (sqrt_bounds(xi[index]**2 + gap[0][0]**2, grid)[0],
                  sqrt_bounds(xi[index]**2 + gap[1][0]**2, grid)[1])
    return critical, gap, index, excitation


def temperature_observations(crystal, prediction, temperatures, tolerance):
    xi, g = crystal.xi, crystal.coupling
    for t in temperatures:
        if prediction is None:
            yield t, None, None
            continue
        normal = critical_bounds(xi, g, t)
        gap = None
        if normal.side == "above_one":
            _, zero_gap, _, _ = prediction
            upper_gap, _ = zero_gap[1]
            grid = ceil(10**12 / min(tolerance, 1, min(map(abs, xi)) * min(1, normal.lo - 1)))
            gap = automatic_bracket(lambda d: thermal_gap_bounds(xi, g, t, d, grid), upper_gap, tolerance)
        yield t, normal, gap


def lean_temperature(index, observation):
    t, normal, gap = observation
    name = f"at{index}"
    lines = [f"def {name} : ℚ := {lean_rat(t)}",
             f"private theorem {name}Positive : 0 < {name} := by decide +kernel"]
    if normal is None:
        return lines + [
            f"theorem {name}_no_gap : ∀ d > 0, thermalResponse levels strength {name} d < 1 := by",
            f"  have ht : (0 : ℝ) < {name} := by exact_mod_cast {name}Positive",
            f"  exact no_thermal_gap levels strength separated ht (prediction.1 _ ht).le", "",
        ]
    if normal.side == "unresolved":
        return []
    if gap is None:
        return lines + [
            f"private def {name}Scale : Site → ℕ := {lean_vec(map(str, normal.witness))}",
            f"theorem {name}_no_gap : ∀ d > 0, thermalResponse levels strength {name} d < 1 := by",
            f"  have ht : (0 : ℝ) < {name} := by exact_mod_cast {name}Positive",
            "  apply no_thermal_gap levels strength separated ht",
            f"  apply le_trans (critical_enclosure levels strength {name} {TERMS} {name}Scale",
            f"    positiveStrength.le {name}Positive (by decide +kernel) (by decide +kernel)).2",
            f"  exact_mod_cast (show criticalUpper levels strength {name} {TERMS} {name}Scale ≤ 1",
            "    from by decide +kernel)", "",
        ]
    for suffix, (d, bound) in zip(("Lo", "Hi"), gap):
        lo, hi, scale_lower, scale_upper = bound.witness
        lines += [
            f"def {name}Delta{suffix} : ℚ := {lean_rat(d)}",
            f"private def {name}{suffix}Lower : Site → ℚ := {lean_vec(map(lean_rat, lo))}",
            f"private def {name}{suffix}Upper : Site → ℚ := {lean_vec(map(lean_rat, hi))}",
            f"private def {name}{suffix}Scale : Site → ℕ := "
            f"{lean_vec(map(str, scale_lower if suffix == 'Lo' else scale_upper))}",
        ]
    return lines + [
        "", "set_option maxHeartbeats 0 in", "set_option maxRecDepth 10000 in",
        f"theorem {name}_gap : ∃ d ∈ Icc ({name}DeltaLo : ℝ) ({name}DeltaHi : ℝ),",
        f"    thermalGapEquation crystal bands {name} (fun _ => d) ∧",
        f"    ∀ x ≥ 0, thermalResponse levels strength {name} x = 1 → x = d := by",
        f"  have ht : (0 : ℝ) < {name} := by exact_mod_cast {name}Positive",
        f"  have hlo : (0 : ℝ) < {name}DeltaLo := by",
        f"    exact_mod_cast (show 0 < {name}DeltaLo from by decide +kernel)",
        f"  have hord : ({name}DeltaLo : ℝ) ≤ {name}DeltaHi := by",
        f"    exact_mod_cast (show {name}DeltaLo ≤ {name}DeltaHi from by decide +kernel)",
        f"  have hl : 1 ≤ thermalResponse levels strength {name} {name}DeltaLo := by",
        f"    apply le_trans _ (thermal_enclosure levels strength {name} {name}DeltaLo",
        f"      {name}LoLower {name}LoUpper positiveStrength.le {name}Positive (by decide +kernel)).1",
        f"    apply le_trans _ (critical_enclosure {name}LoUpper strength {name} {TERMS} {name}LoScale",
        f"      positiveStrength.le {name}Positive (by decide +kernel) (by decide +kernel)).1",
        f"    exact_mod_cast (show 1 ≤ criticalLower {name}LoUpper strength {name} {TERMS} {name}LoScale",
        "      from by decide +kernel)",
        f"  have hu : thermalResponse levels strength {name} {name}DeltaHi ≤ 1 := by",
        f"    apply le_trans (thermal_enclosure levels strength {name} {name}DeltaHi",
        f"      {name}HiLower {name}HiUpper positiveStrength.le {name}Positive (by decide +kernel)).2",
        f"    apply le_trans (critical_enclosure {name}HiLower strength {name} {TERMS} {name}HiScale",
        f"      positiveStrength.le {name}Positive (by decide +kernel) (by decide +kernel)).2",
        f"    exact_mod_cast (show criticalUpper {name}HiLower strength {name} {TERMS} {name}HiScale ≤ 1",
        "      from by decide +kernel)",
        "  obtain ⟨d, hd, he, huniq⟩ :=",
        "    thermal_bracket levels strength separated positiveStrength ht hlo.le hord hl hu",
        "  refine ⟨d, hd, ?_, huniq⟩",
        "  exact (thermal_gap_equation crystal bands strength attraction_channel",
        "    (hlo.trans_le hd.1).ne').2 he", "",
    ]


def lean_source(crystal, prediction, observations):
    hop = lean_vec(map(lean_rat, crystal.hopping))
    coefficients = " ".join(f"({lean_rat(value)})" for value in (
        crystal.stiffness, crystal.deformation, crystal.repulsion, crystal.chemical_potential))
    lines = [
        "/- Generated by scripts/crystal_bcs.py --lean. -/",
        "import Grain.BCSThermal", "", "namespace Grain.CrystalBCS.Certificate", "",
        "open Grain.BCS Set", "",
        f"abbrev Site := Fin {len(crystal.hopping)}",
        f"def crystal : Crystal Site := periodicCrystal {hop} {coefficients}",
        "def bands : BandData Site := periodicBands crystal",
        "def levels : Site → ℚ := xi crystal bands",
        "def strength : ℚ := cooperKernel crystal bands 0 0", "",
        "theorem crystal_parameters : (∀ i, 0 < crystal.stiffness i) ∧",
        "    (∀ i, 0 ≤ crystal.repulsion i) := by decide +kernel",
        "theorem band_basis : normalTest crystal bands := by decide +kernel",
        "theorem attraction_channel : constantChannel crystal bands strength := by decide +kernel",
        "private theorem separated : ∀ i, levels i ≠ 0 := by decide +kernel", "",
    ]
    if prediction is None:
        lines += [
            "theorem prediction : (∀ t > 0, criticalResponse levels strength t < 1) ∧",
            "    (∀ d > 0, zeroResponse levels strength d < 1) := by",
            "  exact subcritical levels strength separated (by decide +kernel)", "",
        ]
    else:
        critical, gap, index, excitation = prediction
        for suffix, (t, bounds) in zip(("Lo", "Hi"), critical):
            scale = lean_vec(map(str, bounds.witness))
            lines += [
                f"def t{suffix} : ℚ := {lean_rat(t)}",
                f"private def scale{suffix} : Site → ℕ := {scale}",
            ]
        for suffix, (delta, bounds) in zip(("Lo", "Hi"), gap):
            lo, hi = (lean_vec(map(lean_rat, values)) for values in bounds.witness)
            lines += [
                f"def delta{suffix} : ℚ := {lean_rat(delta)}",
                f"private def energy{suffix}Lower : Site → ℚ := {lo}",
                f"private def energy{suffix}Upper : Site → ℚ := {hi}",
            ]
        lo, hi = map(lean_rat, excitation)
        lines += [
            f"def excitationLo : ℚ := {lo}",
            f"def excitationHi : ℚ := {hi}", "",
            "private theorem positiveStrength : 0 < strength := by decide +kernel", "",
            "set_option maxRecDepth 10000 in",
            "set_option maxHeartbeats 0 in",
            "theorem critical_temperature : ∃ t ∈ Icc (tLo : ℝ) (tHi : ℝ),",
            "    criticalResponse levels strength t = 1 ∧",
            "    (∀ T > 0, criticalResponse levels strength T = 1 → T = t) ∧",
            "    (∀ T > 0, 1 < criticalResponse levels strength T ↔ T < t) := by",
            "  apply critical_bracket levels strength separated positiveStrength",
            "  · exact_mod_cast (show 0 < tLo from by decide +kernel)",
            "  · exact_mod_cast (show tLo ≤ tHi from by decide +kernel)",
            f"  · apply le_trans _ (critical_enclosure levels strength tLo {TERMS} scaleLo",
            "      positiveStrength.le (by decide +kernel) (by decide +kernel) (by decide +kernel)).1",
            f"    exact_mod_cast (show 1 ≤ criticalLower levels strength tLo {TERMS} scaleLo from by decide +kernel)",
            f"  · apply le_trans (critical_enclosure levels strength tHi {TERMS} scaleHi",
            "      positiveStrength.le (by decide +kernel) (by decide +kernel) (by decide +kernel)).2",
            f"    exact_mod_cast (show criticalUpper levels strength tHi {TERMS} scaleHi ≤ 1 from by decide +kernel)", "",
            "theorem critical_eigenvalue : ∃ t ∈ Icc (tLo : ℝ) (tHi : ℝ),",
            "    IsGreatest (realGrowths crystal bands t) 1 := by",
            "  obtain ⟨t, ht, he, _⟩ := critical_temperature",
            "  refine ⟨t, ht, ?_⟩",
            "  rw [← he]",
            "  have ht₀ : (0 : ℝ) < tLo := by",
            "    exact_mod_cast (show 0 < tLo from by decide +kernel)",
            "  exact leading_normal_growth crystal bands strength attraction_channel",
            "    positiveStrength.le (ht₀.trans_le ht.1)", "",
            "theorem thermal_gap_threshold : ∃ t ∈ Icc (tLo : ℝ) (tHi : ℝ),",
            "    ∀ T > 0, (∃ d > 0, thermalResponse levels strength T d = 1) ↔ T < t := by",
            "  obtain ⟨t, ht, _, _, hsign⟩ := critical_temperature",
            "  exact ⟨t, ht, fun T hT => (positive_gap_iff levels strength separated",
            "    positiveStrength hT).trans (hsign T hT)⟩", "",
            "theorem zero_temperature_gap : ∃ delta ∈ Icc (deltaLo : ℝ) (deltaHi : ℝ),",
            "    zeroGapEquation crystal bands (fun _ => delta) ∧",
            "    (∀ d ≥ 0, zeroResponse levels strength d = 1 → d = delta) ∧",
            "    minimumExcitation levels delta ∈ Icc (excitationLo : ℝ) (excitationHi : ℝ) := by",
            "  have h₀ : (0 : ℝ) < deltaLo := by",
            "    exact_mod_cast (show 0 < deltaLo from by decide +kernel)",
            "  have hord : (deltaLo : ℝ) ≤ deltaHi := by",
            "    exact_mod_cast (show deltaLo ≤ deltaHi from by decide +kernel)",
            "  have hlow : 1 ≤ zeroResponse levels strength (deltaLo : ℝ) := by",
            "    apply le_trans _ (zero_enclosure levels strength deltaLo energyLoLower energyLoUpper",
            "      positiveStrength.le (by decide +kernel)).1",
            "    exact_mod_cast (show 1 ≤ zeroAt energyLoUpper strength from by decide +kernel)",
            "  have hhigh : zeroResponse levels strength (deltaHi : ℝ) ≤ 1 := by",
            "    apply le_trans (zero_enclosure levels strength deltaHi energyHiLower energyHiUpper",
            "      positiveStrength.le (by decide +kernel)).2",
            "    exact_mod_cast (show zeroAt energyHiLower strength ≤ 1 from by decide +kernel)",
            "  obtain ⟨delta, hd, he, hu⟩ :=",
            "    gap_bracket levels strength separated positiveStrength h₀ hord hlow hhigh",
            "  refine ⟨delta, hd, ?_, hu, ?_⟩",
            "  · exact (zero_gap_equation crystal bands strength attraction_channel",
            "      (h₀.trans_le hd.1).ne').2 he",
            f"  · rw [minimum_excitation_eq levels delta {index} (by decide +kernel)]",
            f"    exact excitation_bracket (levels {index}) deltaLo deltaHi excitationLo excitationHi",
            "      hd.1 hd.2 (by decide +kernel) (by decide +kernel) (by decide +kernel)", "",
        ]
    for i, observation in enumerate(observations):
        lines += lean_temperature(i, observation)
    return "\n".join(lines + ["end Grain.CrystalBCS.Certificate", ""])


def report(crystal, prediction, observations, tolerance):
    xi, g = crystal.xi, crystal.coupling
    result = {
        "levels_relative_to_mu_mev": list(map(str, xi)),
        "phonon_induced_onsite_attraction_mev": str(crystal.induced),
        "net_cooper_coupling_mev": str(g),
        "normal_growth_limit": str(g * sum(1 / (2 * abs(level)) for level in xi)),
        "status": "paired" if prediction else "subcritical",
    }
    if prediction:
        critical, gap, _, excitation = prediction
        t, d = (tuple(value for value, _ in endpoints) for endpoints in (critical, gap))
        result.update({
            "critical_kbt_mev": list(map(str, t)),
            "critical_temperature_k_approx": [float(value) / 0.08617333262145 for value in t],
            "pair_potential_at_zero_mev": list(map(str, d)),
            "minimum_excitation_at_zero_mev": list(map(str, excitation)),
            "root_tolerance_met": all(hi - lo <= tolerance for lo, hi in (t, d)),
        })
    result["temperature_observations"] = []
    for t, normal, gap in observations:
        row = {"kbt_mev": str(t)}
        if gap:
            lo, hi = (value for value, _ in gap)
            row.update(status="paired", gap_mev=[str(lo), str(hi)],
                       root_tolerance_met=hi - lo <= tolerance)
        else:
            row["status"] = "unresolved" if normal and normal.side == "unresolved" else "normal"
        result["temperature_observations"].append(row)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("crystal", type=Path)
    parser.add_argument("--accuracy-mev", type=Fraction, default=Fraction("0.000001"))
    parser.add_argument("--at", type=Fraction, nargs="+", default=[], metavar="KBT_MEV",
                        help="also enclose the gap at positive temperatures in units of k_B*T")
    parser.add_argument("--lean", action="store_true", help="emit Lean certificate source")
    args = parser.parse_args()
    if args.accuracy_mev <= 0:
        parser.error("root tolerance must be positive")
    if any(t <= 0 for t in args.at):
        parser.error("temperatures passed to --at must be positive")
    try:
        crystal = read_crystal(args.crystal)
        prediction = predict(crystal, args.accuracy_mev)
        observations = list(temperature_observations(crystal, prediction, args.at, args.accuracy_mev))
        if args.lean:
            print(lean_source(crystal, prediction, observations), end="")
        else:
            print(json.dumps(report(crystal, prediction, observations, args.accuracy_mev), indent=2))
    except (OSError, ValueError, KeyError, TypeError, ZeroDivisionError) as error:
        parser.error(str(error))


if __name__ == "__main__":
    main()
