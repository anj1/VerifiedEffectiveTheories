#!/usr/bin/env python3
"""Emit kernel-checkable certificates for an exported DFPT shell experiment."""
import argparse
from fractions import Fraction as Q
import json
from pathlib import Path

from certify import factor, solve_ones
from dfpt_full_assembly import assemble_full_sector
from dfpt_harmonic import input_source
from dfpt_shell_eft import form, frequency_lower, ground_trial, load, manifest
from fermion import connected_blocks, sector, submatrix
from pairing import lean_rat, lean_vec


def rounded_trial(trial):
    scale = 10**18 / max(map(abs, trial))
    return [round(value * scale) for value in trial]


def matrix_witness(case, electrons, endpoints, tolerance):
    _, _, matrix = assemble_full_sector(case, electrons)
    lo, hi = map(Q, endpoints)
    trial = rounded_trial(ground_trial(matrix, hi + tolerance))
    trial_upper = form(matrix, trial) / sum(value**2 for value in trial)
    electronic = None
    if trial_upper > hi:
        exact = ground_trial(matrix, hi)
        electronic = rounded_trial(exact)
        if form(matrix, electronic) > hi * sum(value**2 for value in electronic):
            electronic = exact

    states = sector(len(case.levels), electrons)
    weights, squares = {}, []
    for indices in connected_blocks(matrix):
        block = submatrix(matrix, indices, indices)
        comparison = [[value if i == j else -abs(value) for j, value in enumerate(row)]
                      for i, row in enumerate(block)]
        if all(sum(row) >= lo for row in comparison):
            continue
        decomposition = factor(comparison, lo)
        if decomposition is None:
            # Certify the signed component itself if absolute values lose
            # cancellations. Lean checks the residual after subtracting LDLᵀ.
            signed = factor(block, lo)
            if signed is None:
                raise ValueError("could not certify the instantaneous lower endpoint")
            lower, pivots = signed
            for j, pivot in enumerate(pivots):
                vector = [(states[i], lower[k][j]) for k, i in enumerate(indices) if lower[k][j]]
                squares.append((pivot, vector))
            continue
        exact = solve_ones(*decomposition)
        scale = 10**26 / max(exact)
        rounded = [round(w * scale) for w in exact]
        if min(rounded) > 0 and all(
            sum(a * x for a, x in zip(row, rounded, strict=True)) >= lo * w
            for row, w in zip(comparison, rounded, strict=True)
        ):
            weights.update(zip(indices, rounded, strict=True))
        else:
            weights.update((i, w * scale) for i, w in zip(indices, exact, strict=True))
    def encode(vector):
        return sorted((state, value) for state, value in zip(states, vector, strict=True) if value)

    return (trial_upper, sorted((states[i], w) for i, w in weights.items()), encode(trial),
            encode(electronic) if electronic is not None else None, squares)


def pair_list(pairs):
    return ", ".join(f"({i}, {lean_rat(a)})" for i, a in pairs)


def mode_terms(case, mode):
    if case.cartesian is None:
        values = mode
    else:
        values = {}
        for weight, axis in zip(mode, case.cartesian, strict=True):
            for key, value in axis.items():
                values[key] = values.get(key, Q(0)) + weight * value
    entries = {(i, j): value for (i, j), value in values.items() if value}
    entries.update({(j, i): value for (i, j), value in values.items() if i != j and value})
    return sorted(entries.items())


def mode_entries(terms):
    return "[" + ", ".join(f"({i}, {j}, {lean_rat(value)})"
                           for (i, j), value in terms) + "]"


def sector_source(case, electrons, bounds, tolerance, allowance):
    n = len(case.levels)
    lo, hi = map(Q, bounds["instantaneous"])
    trial_upper, weights, trial, electronic, squares = matrix_witness(case, electrons, (lo, hi), tolerance)
    harmonic_upper = Q(bounds["parent"][1]) - case.upstream
    name = f"w{electrons}"
    chunks = 2**(2*n) // 64
    if chunks:
        row_proof = (f"  apply all_rows_of_chunks (chunks := {chunks}) rfl\n"
                     "  intro i\n  fin_cases i <;> decide +kernel")
    else:
        row_proof = "  decide +kernel"
    gram = ""
    if squares:
        entries = ", ".join(f"({lean_rat(pivot)}, [{pair_list(vector)}])" for pivot, vector in squares)
        gram = f"\n  squares := [{entries}]"
    trial_data = f"\n  electronicTrial := some [{pair_list(electronic)}]" if electronic else ""
    budget = f"\n  rowBudget := some ({lean_rat(allowance)})" if allowance is not None and not squares else ""
    return f"""def {name} : SectorWitness {n} where
  lower := {lean_rat(lo)}
  electronicUpper := {lean_rat(hi)}
  trialUpper := {lean_rat(trial_upper)}
  harmonicUpper := {lean_rat(harmonic_upper)}
  weights := lookupWeight #[{pair_list(weights)}]
  trial := [{pair_list(trial)}]{trial_data}{gram}{budget}

private theorem {name}Rows :
    ∀ j, rowCheck input modes {electrons} {name} j := by
{row_proof}

theorem bounds{electrons} :
    (({name}.lower : ℝ) ≤ electronicGround input {electrons} ∧
      electronicGround input {electrons} ≤ ({name}.electronicUpper : ℝ)) ∧
    (({name}.lower : ℝ) ≤ harmonicGround input {electrons} ∧
      harmonicGround input {electrons} ≤ ({name}.harmonicUpper : ℝ)) :=
  sector_certificate input input_valid modes modes_valid omega omega_valid {electrons} {name}
    {name}Rows (by decide +kernel)

"""


def case_source(index, raw, case, electrons, validation, tolerance):
    n = len(case.levels)
    m = len(case.modes)
    terms = [mode_terms(case, mode) for _, mode in case.modes]
    modes = lean_vec(mode_entries(entries) for entries in terms)
    allowance = None
    if not case.density and not case.scattering:
        allowance = sum((2 * sum(abs(value) for _, value in entries))**2 / (2 * force)
                        for (force, _), entries in zip(case.modes, terms, strict=True))
    omega = lean_vec(lean_rat(frequency_lower(force)) for force, _ in case.modes)
    sectors = "".join(sector_source(case, k, validation[str(k)], tolerance, allowance) for k in electrons)
    return f"""namespace Case{index}

{input_source(raw)}
def modes : Fin {m} → List (OrbitalEntry {n}) := {modes}
def omega : Fin {m} → ℚ := {omega}

theorem input_valid : Valid input := by decide +kernel

private theorem modes_valid : ∀ j, modes j = modeEntries input j := by decide +kernel

private theorem omega_valid : frequencyTest input omega := by decide +kernel

{sectors}end Case{index}

"""


def contrast_source(label, ground, upper, theorem_index, count, electrons, validation, prediction):
    # Each Fin index identifies one case and one of its three number sectors.
    def table(generate):
        return lean_vec(lean_vec(generate(i, k) for k in electrons) for i in range(count))

    energy = table(lambda i, k: f"{ground} Case{i}.input {k}")
    lows = table(lambda i, k: f"Case{i}.w{k}.lower")
    highs = table(lambda i, k: f"Case{i}.w{k}.{upper}")
    proofs = ", ".join(f"Case{i}.bounds{k}.{theorem_index}"
                       for i in range(count) for k in electrons)
    if label == "harmonic":
        lows = table(lambda i, k: f"(Case{i}.w{k}.lower - Case{i}.upstreamSectorError)")
        highs = table(lambda i, k: f"(Case{i}.w{k}.{upper} + Case{i}.upstreamSectorError)")
    if label == "electronic":
        checks = f"  exacts [{proofs}]"
    else:
        checks = "\n".join(f"  · exact widen_bounds (budget := Case{i}.upstreamSectorError) (by decide +kernel) Case{i}.bounds{k}.{theorem_index}"
                           for i in range(count) for k in electrons)
    vlo, vhi = map(Q, validation)
    plo, phi = map(Q, prediction)
    sign = ""
    if vlo > 0:
        sign = (f"theorem {label}_positive : 0 < {label}Contrast :=\n"
                f"  lt_of_lt_of_le (by norm_num) {label}_validation.1\n\n")
    elif vhi < 0:
        sign = (f"theorem {label}_negative : {label}Contrast < 0 :=\n"
                f"  lt_of_le_of_lt {label}_validation.2 (by norm_num)\n\n")
    vlo, vhi, plo, phi = (lean_rat(x) for x in (vlo, vhi, plo, phi))
    return f"""noncomputable def {label}Energy (a : Index) : ℝ := ({energy} a.1) a.2

private def {label}Lo (a : Index) : ℚ := ({lows} a.1) a.2
private def {label}Hi (a : Index) : ℚ := ({highs} a.1) a.2

theorem {label}_sectors (a : Index) :
    ({label}Lo a : ℝ) ≤ {label}Energy a ∧ {label}Energy a ≤ ({label}Hi a : ℝ) := by
  obtain ⟨i, j⟩ := a
  fin_cases i <;> fin_cases j
{checks}

noncomputable def {label}Contrast : ℝ :=
  ∑ a, (weight a : ℝ) * {label}Energy a

theorem {label}_validation :
    (({vlo} : ℚ) : ℝ) ≤ {label}Contrast ∧ {label}Contrast ≤ (({vhi} : ℚ) : ℝ) :=
  certified_contrast weight {label}Lo {label}Hi {label}Energy {label}_sectors ({vlo}) ({vhi})
    (by decide +kernel) (by decide +kernel)

theorem {label}_prediction :
    (({plo} : ℚ) : ℝ) ≤ {label}Contrast ∧ {label}Contrast ≤ (({phi} : ℚ) : ℝ) := by
  have hlo : ({plo} : ℚ) ≤ ({vlo} : ℚ) := by decide +kernel
  have hhi : ({vhi} : ℚ) ≤ ({phi} : ℚ) := by decide +kernel
  exact ⟨(by exact_mod_cast hlo : (({plo} : ℚ) : ℝ) ≤ (({vlo} : ℚ) : ℝ)).trans {label}_validation.1,
    {label}_validation.2.trans (by exact_mod_cast hhi)⟩


{sign}"""


def lean_source(path, frozen, validation, namespace, split=False, case_index=None):
    cases, odd, active, weights, tolerance = load(path)
    raw = json.loads(path.read_text(), parse_float=Q)
    if frozen["manifest"] != manifest(path):
        raise ValueError("frozen input or prediction code changed")
    prediction = frozen["prediction"]
    electrons = (odd - 1, odd, odd + 1)
    imports = "import Grain.DFPTCertificate"
    if split and case_index is None:
        imports = "\n".join(f"import Grain.{namespace}.Case{i}" for i in range(len(cases)))
    header = f"""{imports}

/- Generated by scripts/dfpt_certificate.py from the exported inputs and their recorded intervals. -/

namespace Grain.HarmonicBand.{namespace}

open scoped BigOperators

set_option maxRecDepth 10000
set_option maxHeartbeats 0

"""
    if case_index is not None:
        if not 0 <= case_index < len(cases):
            raise ValueError("case index is outside the declared exports")
        name, case = list(cases.items())[case_index]
        return (header + case_source(case_index, raw["cases"][name], case, electrons,
                                     validation["sectors"][name], tolerance / 32)
                + f"end Grain.HarmonicBand.{namespace}\n")
    case_modules = "" if split else "".join(
        case_source(i, raw["cases"][name], case, electrons, validation["sectors"][name], tolerance / 32)
        for i, (name, case) in enumerate(cases.items()))
    count = len(cases)
    weight_vec = lean_vec(lean_rat(w) for w in weights.values())
    orbitals = lean_vec(str(len(case.levels)) for case in cases.values())
    return header + f"""{case_modules}abbrev Index := Fin {count} × Fin 3

def oddElectrons : ℕ := {odd}
def activeOrbitals : ℕ := {active}
def energyResolution : ℚ := {lean_rat(tolerance)}

def caseWeight : Fin {count} → ℚ := {weight_vec}
def weight (a : Index) : ℚ := caseWeight a.1 * (![-1/2, 1, -1/2] : Fin 3 → ℚ) a.2

theorem export_parameters :
    oddElectrons % 2 = 1 ∧ 0 < energyResolution ∧
    (∀ i : Fin {count}, oddElectrons < 2 * ({orbitals} : Fin {count} → ℕ) i ∧
      0 < activeOrbitals ∧ activeOrbitals ≤ ({orbitals} : Fin {count} → ℕ) i) ∧
    (∑ i, caseWeight i) = 0 := by decide +kernel

{contrast_source("electronic", "electronicGround", "electronicUpper", 1, count, electrons,
                 validation["instantaneous_contrast_mev"], prediction["instantaneous_contrast_mev"])}
{contrast_source("harmonic", "harmonicGround", "harmonicUpper", 2, count, electrons,
                 validation["parent_contrast_mev"], prediction["parent_contrast_mev"])}
end Grain.HarmonicBand.{namespace}
"""


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path)
    parser.add_argument("prediction", type=Path)
    parser.add_argument("validation", type=Path)
    parser.add_argument("--namespace", default="DFPTExport")
    parts = parser.add_mutually_exclusive_group()
    parts.add_argument("--split", action="store_true", help="emit the module importing the case certificates")
    parts.add_argument("--case-index", type=int, help="emit one zero-based case certificate module")
    args = parser.parse_args()
    if not args.namespace.isidentifier():
        parser.error("namespace must be a Lean identifier")
    try:
        print(lean_source(args.input, json.loads(args.prediction.read_text()),
                          json.loads(args.validation.read_text()), args.namespace,
                          args.split, args.case_index), end="")
    except (ArithmeticError, KeyError, TypeError, ValueError, OSError) as error:
        parser.error(str(error))


if __name__ == "__main__":
    main()
