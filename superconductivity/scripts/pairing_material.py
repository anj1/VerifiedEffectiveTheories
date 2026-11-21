#!/usr/bin/env python3
"""Certify pairing against input uncertainty and omitted finite frequency rows."""
import argparse
from dataclasses import dataclass
from fractions import Fraction as Q
import json
from math import ceil, floor, pi
from pathlib import Path

from pairing import crossing, eigenvalue_bounds, lean_rat, lean_vec, rational, shifted_factor


@dataclass(frozen=True)
class Box:
    lo: Q
    hi: Q

    def __add__(self, other):
        return Box(self.lo + other.lo, self.hi + other.hi)

    def __sub__(self, other):
        return Box(self.lo - other.hi, self.hi - other.lo)

    def times_positive(self, other):
        return Box(self.lo * other.lo, self.hi * other.hi)

    def over_positive(self, other):
        return Box(self.lo / other.hi, self.hi / other.lo)

    @property
    def mid(self):
        return (self.lo + self.hi) / 2

    def radius(self, center):
        return max(abs(self.lo - center), abs(self.hi - center))


def point(x):
    return Box(Q(x), Q(x))


def read_box(raw):
    if isinstance(raw, list):
        lo, hi = map(rational, raw)
    else:
        lo = hi = rational(raw)
    if lo > hi:
        raise ValueError("interval endpoints must be ordered")
    return Box(lo, hi)


def window_sample(energy, weight, width):
    if -width <= energy.lo and energy.hi <= width:
        return point(weight)
    if energy.hi < -width or width < energy.lo:
        return point(0)
    return Box(Q(0), weight)


@dataclass(frozen=True)
class Mesh:
    width: Q
    patches: tuple
    modes: tuple
    coulomb: tuple

    @property
    def weights(self):
        return tuple(sum((window_sample(energy, w, self.width) for energy, w in patch), point(0))
                     .over_positive(point(2 * self.width)) for patch in self.patches)


def read_mesh(path):
    data = json.loads(path.read_text(), parse_float=Q)
    width = rational(data["fermi_halfwidth_mev"])
    if width <= 0 or not isinstance(data["patches"], list) or not data["patches"]:
        raise ValueError("need a positive Fermi half width and nonempty patches array")
    patches = []
    for patch in data["patches"]:
        if not isinstance(patch, list):
            raise ValueError("patches must be arrays of band samples")
        rows = tuple((read_box(row["xi_mev"]), rational(row["quadrature_weight"])) for row in patch)
        if any(w < 0 for _, w in rows):
            raise ValueError("quadrature weights must be nonnegative")
        patches.append(rows)

    count = len(patches)
    modes = [[() for _ in patches] for _ in patches]
    coulomb = [[point(0) for _ in patches] for _ in patches]
    seen = set()
    if not isinstance(data["transitions"], list):
        raise ValueError("transitions must be a JSON array")
    for entry in data["transitions"]:
        i, j = entry["patches"]
        if any(type(k) is not int or not 0 <= k < count for k in (i, j)):
            raise ValueError("transition patch index out of range")
        pair = min(i, j), max(i, j)
        if pair in seen:
            raise ValueError(f"repeated transition {pair}")
        seen.add(pair)
        if not isinstance(entry["modes"], list):
            raise ValueError("each transition must have an array of modes")
        repulsion = read_box(entry["coulomb_mev"])
        branches = tuple((read_box(m["energy_mev"]), read_box(m["vertex_sq_mev2"]))
                         for m in entry["modes"])
        if repulsion.lo < 0 or any(energy.lo <= 0 or vertex.lo < 0 for energy, vertex in branches):
            raise ValueError("need positive phonon energies and nonnegative vertices squared and repulsion")
        modes[i][j] = modes[j][i] = branches
        coulomb[i][j] = coulomb[j][i] = repulsion
    mesh = Mesh(width, tuple(patches), tuple(map(tuple, modes)), tuple(map(tuple, coulomb)))
    if any(w.lo <= 0 for w in mesh.weights):
        raise ValueError("each patch must have positive certified weight inside the Fermi window")
    return mesh


def phonon_box(modes, transfer_sq):
    return sum((point(2).times_positive(e).times_positive(vertex)
                .over_positive(e.times_positive(e) + point(transfer_sq))
                for e, vertex in modes), point(0))


def assemble_boxes(mesh, frequencies, cutoff, tau):
    if tau <= 0:
        raise ValueError("pi*k_B*T must be positive")
    weights = mesh.weights
    phonon = {
        (i, j): [phonon_box(mesh.modes[i][j], (2 * tau * k)**2) for k in range(2 * frequencies)]
        for i in range(len(weights)) for j in range(i, len(weights))
    }
    grid = [(i, n) for i in range(len(weights)) for n in range(frequencies)]
    kernel, metric = [], []
    for i, n in grid:
        row = []
        normal = point(2 * n + 1)
        for j, m in grid:
            values = phonon[min(i, j), max(i, j)]
            difference, total = values[abs(n - m)], values[n + m + 1]
            attraction = difference + total
            if n < cutoff and m < cutoff:
                attraction -= point(2).times_positive(mesh.coulomb[i][j])
            row.append(attraction)
            delta = difference - total
            normal += weights[j].times_positive(Box(max(0, delta.lo), delta.hi))
        kernel.append(row)
        metric.append(normal.over_positive(weights[i]))
    return kernel, metric


@dataclass(frozen=True)
class Result:
    nominal_lo: Q
    nominal_hi: Q
    lo: Q
    hi: Q
    error: list
    trial: list
    lower: list
    pivots: list

    @property
    def side(self):
        if self.lo > 1:
            return "above_one"
        if self.hi < 1:
            return "below_one"
        return "unresolved"


def solve_material(mesh, retained, frequencies, cutoff, tau, digits):
    boxes, metric = assemble_boxes(mesh, frequencies, cutoff, tau)
    d = [val.mid for val in metric]
    size = len(d)
    keep = [i for i in range(size) if i % frequencies < retained]
    head = [[boxes[i][j].mid for j in keep] for i in keep]
    head_metric = [d[i] for i in keep]
    cert = eigenvalue_bounds(head, head_metric, digits)

    # The reference pencil is the retained solve padded with zero interaction.
    pos = {i: k for k, i in enumerate(keep)}
    trial = [cert.trial[pos[i]] if i in pos else Q(0) for i in range(size)]
    radii = [[box.radius(box.mid if i in pos and j in pos else Q(0))
              for j, box in enumerate(row)] for i, row in enumerate(boxes)]
    grid = 10**digits
    error = [Q(ceil(grid * sum((radii[i][j] + radii[j][i]) / 2 for j in range(size))), grid)
             for i in range(size)]

    # The upper matrix has a diagonal correction in every row. The
    # complementary block is diagonal and needs no eigensolve.
    bounded_head = [[head[k][l] + (error[i] if k == l else 0) for l in range(len(keep))]
                    for k, i in enumerate(keep)]
    upper_metric = [box.lo for box in metric]
    tail_top = max((error[i] / upper_metric[i] for i in range(size) if i not in pos), default=None)
    kept_upper = eigenvalue_bounds(bounded_head, [upper_metric[i] for i in keep], digits)
    if tail_top is None and kept_upper.hi < 0:
        upper_metric = [box.hi for box in metric]
        kept_upper = eigenvalue_bounds(bounded_head, upper_metric, digits)
        # A signed upper endpoint uses the upper metric interval. Rounding
        # it to zero is also sound and the zero shift is metric independent.
    hi = kept_upper.hi
    if tail_top is not None:
        hi = max(hi, Q(ceil(tail_top * grid), grid))
    lower, pivot = (kept_upper.lower, kept_upper.pivots) if hi == kept_upper.hi else shifted_factor(
        bounded_head, [upper_metric[i] for i in keep], hi)[0]
    extended_lower = [[lower[pos[i]][pos[j]] if i in pos and j in pos else Q(int(i == j))
                       for j in range(size)] for i in range(size)]
    extended_pivot = [pivot[pos[i]] if i in pos else hi * upper_metric[i] - error[i]
                      for i in range(size)]

    # Zero padding leaves all discarded entries out of the lower trial.
    trial_energy = sum((box.lo if product >= 0 else box.hi) * product
                       for i, row in enumerate(boxes)
                       for j, box in enumerate(row)
                       if (product := trial[i] * trial[j]))
    trial_norm = sum((box.hi if trial_energy >= 0 else box.lo) * x**2 for box, x in zip(metric, trial))
    lo_out = Q(floor(grid * trial_energy / trial_norm), grid)
    return Result(cert.lo, cert.hi, lo_out, hi, error, trial, extended_lower, extended_pivot)


def observation(t, result):
    return {
        "pi_kbt_mev": str(t),
        "temperature_k_approx": float(t) / (pi * 0.08617333262145),
        "retained_eigenvalue_at_midpoints": [str(result.nominal_lo), str(result.nominal_hi)],
        "kernel_row_allowances_mev": list(map(str, result.error)),
        "enclosed_eigenvalue": [str(result.lo), str(result.hi)],
        "threshold": result.side,
    }


def lean_box(box):
    return f"⟨{lean_rat(box.lo)}, {lean_rat(box.hi)}⟩"


def lean_list(items):
    return "[" + ", ".join(items) + "]"


def lean_source(mesh, retained, frequencies, cutoff, results, bracket):
    def grid(values):
        return lean_vec(lean_vec(values[i:i + frequencies])
                        for i in range(0, len(values), frequencies))

    bands = lean_vec(lean_list(f"⟨{lean_box(e)}, {lean_rat(w)}⟩" for e, w in patch) for patch in mesh.patches)
    modes = lean_vec(lean_vec(lean_list(f"⟨{lean_box(e)}, {lean_box(v)}⟩" for e, v in branch)
                              for branch in row) for row in mesh.modes)
    coulomb = lean_vec(lean_vec(map(lean_box, row)) for row in mesh.coulomb)
    lines = [
        "/- Generated by scripts/pairing_material.py --lean. -/",
        "import Grain.PairingCrossing", "", "namespace Grain.Pairing.Material.Certificate", "",
        f"abbrev Patch := Fin {len(mesh.patches)}",
        f"abbrev Grid := Patch × Fin {frequencies}", "",
        "def mesh : Mesh Patch where",
        f"  halfWidth := {lean_rat(mesh.width)}",
        f"  bands := {bands}",
        f"  modes i j := ({modes}) i j",
        f"  coulomb i j := ({coulomb}) i j", "",
        "theorem has_realization : ∃ r, mesh.matches r :=",
        "  ⟨midpointRealization mesh, midpoint_realizes mesh (by decide +kernel)⟩", "",
    ]
    for i, (t, cert) in enumerate(results):
        lo, hi = lean_rat(cert.lo), lean_rat(cert.hi)
        lines += [
            f"def tau{i} : ℚ := {lean_rat(t)}",
            f"def A{i} : Grid → Grid → ℚ := referenceKernel mesh {retained} {cutoff} tau{i}",
            f"def Fbox{i} : Grid → Grid → Interval := kernelBox mesh {cutoff} tau{i}",
            f"def Dbox{i} : Grid → Interval := metricBox mesh tau{i}",
            f"def lo{i} : ℚ := {lo}",
            f"def hi{i} : ℚ := {hi}",
            f"def err{i} : Grid → ℚ := fun a => ({grid(list(map(lean_rat, cert.error)))}) a.1 a.2", "",
            f"private def x{i} : Grid → ℚ := fun a => ({grid(list(map(lean_rat, cert.trial)))}) a.1 a.2",
            f"private def pivots{i} : Grid → ℚ := fun a => ({grid(list(map(lean_rat, cert.pivots)))}) a.1 a.2",
            f"private def L{i} : Grid → Grid → ℚ := fun a b =>",
            f"  ({grid([grid(list(map(lean_rat, row))) for row in cert.lower])}) a.1 a.2 b.1 b.2", "",
            "set_option maxHeartbeats 0 in",
            "set_option maxRecDepth 15000 in",
            f"theorem bounds{i} (r : Realization Patch) (h : mesh.matches r) :",
            f"    (lo{i} : ℝ) ≤ spectrumTop (meshKernel r {cutoff} tau{i})",
            f"      (meshMetric mesh r tau{i} : Grid → ℝ) ∧",
            f"    spectrumTop (meshKernel r {cutoff} tau{i}) (meshMetric mesh r tau{i} : Grid → ℝ) ≤",
            f"      (hi{i} : ℝ) := by",
            f"  have hl : trialTest Fbox{i} Dbox{i} lo{i} x{i} := by decide +kernel",
            f"  have hu : upperTest (upperKernel A{i} err{i}) (metricEndpoint Dbox{i} hi{i})",
            f"    hi{i} L{i} pivots{i} := by decide +kernel",
            f"  have he : ∀ a, radiusRow Fbox{i} A{i} a ≤ err{i} a := by decide +kernel",
            f"  exact material_spectrum_enclosure mesh r h (by decide +kernel) (by decide +kernel)",
            f"    tau{i} {retained} {cutoff} lo{i} hi{i} err{i} x{i} L{i} pivots{i} hl hu he", "",
        ]
    if bracket:
        l, h = len(results) - 2, len(results) - 1
        lines += [
            "theorem crossing_endpoints (r : Realization Patch) (h : mesh.matches r) :",
            f"    0 < tau{l} ∧ tau{l} < tau{h} ∧",
            f"    1 < spectrumTop (meshKernel r {cutoff} tau{l}) (meshMetric mesh r tau{l} : Grid → ℝ) ∧",
            f"    spectrumTop (meshKernel r {cutoff} tau{h}) (meshMetric mesh r tau{h} : Grid → ℝ) < 1 := by",
            "  refine ⟨by decide +kernel, by decide +kernel, ?_, ?_⟩",
            f"  · have hl : 1 < lo{l} := by decide +kernel",
            f"    exact lt_of_lt_of_le (by exact_mod_cast hl) (bounds{l} r h).1",
            f"  · have hu : hi{h} < 1 := by decide +kernel",
            f"    exact lt_of_le_of_lt (bounds{h} r h).2 (by exact_mod_cast hu)", "",
            "theorem crossing (r : Realization Patch) (h : mesh.matches r) :",
            f"    ∃ t ∈ Set.Icc (tau{l} : ℝ) (tau{h} : ℝ),",
            f"      spectrumTop (meshKernel r {cutoff} t) (meshMetric mesh r t : Grid → ℝ) = 1 := by",
            "  obtain ⟨_, hord, hl, hu⟩ := crossing_endpoints r h",
            f"  exact mesh_crossing mesh r h (by decide +kernel) (by decide +kernel) {cutoff}",
            "    (by exact_mod_cast hord.le) hl.le hu.le", "",
            "theorem pairing_instability (r : Realization Patch) (h : mesh.matches r)",
            "    (hm : ∀ i j, r.modes i j = r.modes j i)",
            "    (hc : ∀ i j, r.coulomb i j = r.coulomb j i) :",
            f"    ∃ t ∈ Set.Icc (tau{l} : ℝ) (tau{h} : ℝ), ∃ x : Grid → ℝ, x ≠ 0 ∧",
            f"      ∀ a, (∑ b, meshKernel r {cutoff} t a b * x b) = meshMetric mesh r t a * x a := by",
            "  obtain ⟨t, ht, he⟩ := crossing r h",
            f"  obtain ⟨x, hx, hresponse⟩ := spectrum_eigenvector (meshKernel r {cutoff} t)",
            "    (meshMetric mesh r t : Grid → ℝ)",
            f"    (mesh_kernel_symm r {cutoff} t hm hc)",
            "    (mesh_metric_pos mesh r h (by decide +kernel) (by decide +kernel) t)",
            "  exact ⟨t, ht, x, hx, fun a => by simpa [he] using hresponse a⟩", "",
        ]
    return "\n".join(lines + ["end Grain.Pairing.Material.Certificate", ""])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mesh", type=Path)
    parser.add_argument("--retained-frequencies", type=int, required=True)
    parser.add_argument("--checked-frequencies", type=int, required=True)
    parser.add_argument("--coulomb-frequencies", type=int, required=True)
    parser.add_argument("--at", type=Q, nargs="+", default=[], metavar="PI_KBT_MEV")
    parser.add_argument("--bracket", type=Q, nargs=2, metavar=("COLD", "HOT"))
    parser.add_argument("--temperature-tolerance", type=Q, default=Q("0.001"))
    parser.add_argument("--digits", type=int, default=7)
    parser.add_argument("--lean", action="store_true", help="print a Lean certificate instead of JSON")
    args = parser.parse_args()
    retained, checked, cutoff = args.retained_frequencies, args.checked_frequencies, args.coulomb_frequencies
    if not 0 < retained <= checked or cutoff < 0 or args.digits < 1:
        parser.error("need 0 < retained frequencies <= checked frequencies, nonnegative cutoff, positive digits")
    if not args.at and not args.bracket:
        parser.error("provide at least one temperature with --at or a --bracket")
    try:
        mesh = read_mesh(args.mesh)

        def solve(tau):
            return solve_material(mesh, retained, checked, cutoff, tau, args.digits)

        observations = [(t, solve(t)) for t in args.at]
        bracket = crossing(solve, *args.bracket, args.temperature_tolerance) if args.bracket else []
        if args.lean:
            print(lean_source(mesh, retained, checked, cutoff, observations + bracket, bracket), end="")
        else:
            report = {
                "patch_dos_per_mev": [[str(w.lo), str(w.hi)] for w in mesh.weights],
                "retained_frequencies": retained,
                "checked_frequencies": checked,
                "coulomb_frequencies": cutoff,
                "observations": [observation(*row) for row in observations],
            }
            if bracket:
                report["crossing_bracket"] = [observation(*row) for row in bracket]
                report["temperature_tolerance_met"] = bracket[1][0] - bracket[0][0] <= args.temperature_tolerance
            print(json.dumps(report, indent=2))
    except (OSError, ValueError, KeyError, TypeError, ZeroDivisionError) as error:
        parser.error(str(error))


if __name__ == "__main__":
    main()
