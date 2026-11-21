#!/usr/bin/env python3
"""Assemble and certify the finite even-frequency pairing eigenproblem."""
import argparse
from dataclasses import dataclass
from fractions import Fraction
import json
from math import ceil, floor, pi
from pathlib import Path

from certify import matvec


@dataclass(frozen=True)
class ElectronicData:
    weights: tuple
    modes: tuple
    coulomb: tuple


def rational(value):
    if type(value) not in (int, str, Fraction):
        raise ValueError("expected an exact number such as 2, \"0.02\" or \"1/50\"")
    return Fraction(value)


def read_data(path):
    data = json.loads(path.read_text(), parse_float=Fraction)
    if not isinstance(data["patch_weights_per_mev"], list) or not isinstance(data["transitions"], list):
        raise ValueError("patch weights and transitions must be JSON arrays")
    weights = tuple(map(rational, data["patch_weights_per_mev"]))
    if not weights or min(weights) <= 0:
        raise ValueError("patch weights must be positive and the patch list nonempty")
    count = len(weights)
    modes = [[() for _ in weights] for _ in weights]
    coulomb = [[Fraction(0) for _ in weights] for _ in weights]
    seen = set()
    for entry in data["transitions"]:
        i, j = entry["patches"]
        if any(type(k) is not int or not 0 <= k < count for k in (i, j)):
            raise ValueError("transition patch index out of range")
        pair = min(i, j), max(i, j)
        if pair in seen:
            raise ValueError(f"repeated transition {pair}")
        seen.add(pair)
        repulsion = rational(entry["coulomb_mev"])
        if not isinstance(entry["modes"], list):
            raise ValueError("each transition must have a JSON array of phonon modes")
        branches = tuple((rational(mode["energy_mev"]), rational(mode["vertex_sq_mev2"]))
                         for mode in entry["modes"])
        if repulsion < 0 or any(energy <= 0 or vertex_sq < 0 for energy, vertex_sq in branches):
            raise ValueError("need positive phonon energies and nonnegative vertices squared and repulsion")
        modes[i][j] = modes[j][i] = branches
        coulomb[i][j] = coulomb[j][i] = repulsion
    return ElectronicData(weights, tuple(map(tuple, modes)), tuple(map(tuple, coulomb)))


def assemble(data, frequencies, tau):
    """Return the real symmetric kernel F and the positive diagonal metric D."""
    if frequencies < 1 or tau <= 0:
        raise ValueError("need at least one positive frequency and positive pi*k_B*T")
    count = len(data.weights)
    phonon = {
        (i, j): [
            sum((2 * energy * vertex_sq / (energy**2 + (2 * tau * k)**2)
                 for energy, vertex_sq in data.modes[i][j]), Fraction(0))
            for k in range(2 * frequencies)
        ]
        for i in range(count) for j in range(i, count)
    }
    grid = [(i, n) for i in range(count) for n in range(frequencies)]
    matrix, metric = [], []
    for i, n in grid:
        row = []
        normal = Fraction(0)
        for j, m in grid:
            values = phonon[min(i, j), max(i, j)]
            difference, total = values[abs(n - m)], values[n + m + 1]
            row.append(difference + total - 2 * data.coulomb[i][j])
            normal += data.weights[j] * (difference - total)
        matrix.append(row)
        # Z = 1 + normal / (2n+1), and the pair weight is N_i / (2n+1).
        metric.append((2 * n + 1 + normal) / data.weights[i])
    return matrix, metric


def shifted_factor(matrix, metric, shift):
    """Return an LDLᵀ factor or a nonzero x with xᵀ(F - shift D)x ≥ 0."""
    size = len(metric)
    lower = [[Fraction(int(i == j)) for j in range(size)] for i in range(size)]
    pivots = []
    for j in range(size):
        pivot = shift * metric[j] - matrix[j][j] - sum(
            lower[j][k] ** 2 * pivots[k] for k in range(j))
        if pivot <= 0:
            # In this principal block Lᵀ x = e_j. Its shifted form is the failed pivot.
            trial = [Fraction(0)] * size
            trial[j] = Fraction(1)
            for i in reversed(range(j)):
                trial[i] = -sum(lower[k][i] * trial[k] for k in range(i + 1, j + 1))
            return None, trial
        pivots.append(pivot)
        for i in range(j + 1, size):
            lower[i][j] = (-matrix[i][j] - sum(
                lower[i][k] * pivots[k] * lower[j][k] for k in range(j))) / pivot
    return (lower, pivots), None


@dataclass(frozen=True)
class Bounds:
    lo: Fraction
    hi: Fraction
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


def eigenvalue_bounds(matrix, metric, digits):
    grid = 10**digits
    lo = floor(grid * max(row[i] / metric[i] for i, row in enumerate(matrix)))
    hi = ceil(grid * max((row[i] + sum(abs(value) for j, value in enumerate(row) if j != i))
                         / metric[i] for i, row in enumerate(matrix))) + 1
    factor, _ = shifted_factor(matrix, metric, Fraction(hi, grid))
    _, trial = shifted_factor(matrix, metric, Fraction(lo, grid))
    while hi - lo > 1:
        mid = (lo + hi) // 2
        candidate, witness = shifted_factor(matrix, metric, Fraction(mid, grid))
        if candidate is None:
            lo, trial = mid, witness
        else:
            hi, factor = mid, candidate
    lower, pivots = factor
    lo, hi = Fraction(lo, grid), Fraction(hi, grid)
    # Check the returned witnesses independently of the search.
    norm = sum(d * x**2 for d, x in zip(metric, trial))
    if norm <= 0 or sum(x * y for x, y in zip(trial, matvec(matrix, trial))) < lo * norm:
        raise ArithmeticError("invalid lower eigenvalue witness")
    if min(pivots) <= 0 or any(
        (hi * metric[i] if i == j else 0) - matrix[i][j] !=
        sum(lower[i][k] * pivots[k] * lower[j][k] for k in range(len(metric)))
        for i in range(len(metric)) for j in range(i + 1)
    ):
        raise ArithmeticError("invalid upper eigenvalue witness")
    return Bounds(lo, hi, trial, lower, pivots)


def crossing(solve, cold, hot, tolerance):
    if not 0 < cold < hot or tolerance <= 0:
        raise ValueError("need 0 < cold < hot and a positive temperature tolerance")
    low, high = solve(cold), solve(hot)
    if low.side != "above_one" or high.side != "below_one":
        raise ValueError("bracket requires a certified eigenvalue above one at cold and below one at hot")
    while hot - cold > tolerance:
        mid = (cold + hot) / 2
        bounds = solve(mid)
        if bounds.side == "above_one":
            cold, low = mid, bounds
        elif bounds.side == "below_one":
            hot, high = mid, bounds
        else:
            # An exact or numerically unresolved crossing at the midpoint can still be
            # bracketed more tightly using strict signs on either side.
            left, right = (cold + mid) / 2, (mid + hot) / 2
            left_bounds, right_bounds = solve(left), solve(right)
            if left_bounds.side == "above_one" and right_bounds.side == "below_one":
                cold, low, hot, high = left, left_bounds, right, right_bounds
            elif left_bounds.side == "above_one":
                cold, low = left, left_bounds
            elif right_bounds.side == "below_one":
                hot, high = right, right_bounds
            else:
                break
    return [(cold, low), (hot, high)]


def observation(tau, bounds):
    return {
        "pi_kbt_mev": str(tau),
        "temperature_k_approx": float(tau) / (pi * 0.08617333262145),
        "eigenvalue": [str(bounds.lo), str(bounds.hi)],
        "threshold": bounds.side,
    }


def lean_rat(value):
    return f"({value})" if value < 0 else str(value)


def lean_vec(values):
    return "![" + ", ".join(values) + "]"


def lean_source(data, frequencies, results, bracket):
    def grid(values):
        return lean_vec(lean_vec(values[i:i + frequencies])
                        for i in range(0, len(values), frequencies))

    weights = lean_vec(map(lean_rat, data.weights))
    modes = lean_vec(lean_vec(
        "[" + ", ".join(f"⟨{lean_rat(energy)}, {lean_rat(vertex_sq)}⟩"
                        for energy, vertex_sq in entry) + "]" for entry in row)
        for row in data.modes)
    coulomb = lean_vec(lean_vec(map(lean_rat, row)) for row in data.coulomb)
    lines = [
        "/- Generated by scripts/pairing.py --lean. -/",
        "import Grain.Pairing", "", "namespace Grain.Pairing.Certificate", "",
        f"abbrev Patch := Fin {len(data.weights)}",
        f"abbrev Grid := Patch × Fin {frequencies}", "",
        "def data : Input Patch where",
        f"  weight := {weights}",
        f"  modes i j := ({modes}) i j",
        f"  coulomb i j := ({coulomb}) i j", "",
    ]
    for index, (tau, cert) in enumerate(results):
        lo, hi = lean_rat(cert.lo), lean_rat(cert.hi)
        lines += [
            f"def tau{index} : ℚ := {lean_rat(tau)}",
            f"def F{index} : Grid → Grid → ℚ := kernel data tau{index}",
            f"def D{index} : Grid → ℚ := metric data tau{index}", "",
            f"private def x{index} : Grid → ℚ := fun a => ({grid(list(map(lean_rat, cert.trial)))}) a.1 a.2",
            f"private def pivots{index} : Grid → ℚ := fun a => ({grid(list(map(lean_rat, cert.pivots)))}) a.1 a.2",
            f"private def L{index} : Grid → Grid → ℚ := fun a b =>",
            f"  ({grid([grid(list(map(lean_rat, row))) for row in cert.lower])}) a.1 a.2 b.1 b.2",
            "",
            "set_option maxHeartbeats 0 in",
            "set_option maxRecDepth 10000 in",
            f"theorem bounds{index} : 0 < tau{index} ∧ (∀ a, 0 < D{index} a) ∧",
            f"    (({lo} : ℚ) : ℝ) ≤ leading F{index} D{index} ∧ leading F{index} D{index} ≤ (({hi} : ℚ) : ℝ) := by",
            f"  exact ⟨by decide +kernel, by decide +kernel,",
            f"    eigenvalue_bounds F{index} D{index} ({lo}) ({hi}) x{index} L{index} pivots{index}",
            "      (by decide +kernel) (by decide +kernel)⟩", "",
        ]
    if bracket:
        left, right = len(results) - 2, len(results) - 1
        lines += [
            "theorem crossing_endpoints :",
            f"    tau{left} < tau{right} ∧ 1 < leading F{left} D{left} ∧",
            f"      leading F{right} D{right} < 1 := by",
            "  refine ⟨by decide +kernel, ?_, ?_⟩",
            f"  · exact lt_of_lt_of_le (by norm_num) bounds{left}.2.2.1",
            f"  · exact lt_of_le_of_lt bounds{right}.2.2.2 (by norm_num)", "",
        ]
    return "\n".join(lines + ["end Grain.Pairing.Certificate", ""])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("data", type=Path)
    parser.add_argument("--positive-frequencies", type=int, required=True)
    parser.add_argument("--at", type=Fraction, nargs="+", default=[], metavar="PI_KBT_MEV")
    parser.add_argument("--bracket", type=Fraction, nargs=2, metavar=("COLD", "HOT"),
                        help="find a crossing bracket in units of pi*k_B*T (meV)")
    parser.add_argument("--temperature-tolerance", type=Fraction, default=Fraction("0.001"),
                        help="target width of the crossing bracket in meV")
    parser.add_argument("--digits", type=int, default=8, help="decimal places in eigenvalue bounds")
    parser.add_argument("--lean", action="store_true", help="print a Lean certificate instead of JSON")
    args = parser.parse_args()
    if args.positive_frequencies < 1 or args.digits < 1:
        parser.error("positive frequencies and digits must be positive")
    if not args.at and not args.bracket:
        parser.error("provide at least one temperature with --at or a --bracket")
    try:
        data = read_data(args.data)

        def solve(tau):
            return eigenvalue_bounds(*assemble(data, args.positive_frequencies, tau), args.digits)

        observations = [(tau, solve(tau)) for tau in args.at]
        bracket = crossing(solve, *args.bracket, args.temperature_tolerance) if args.bracket else []
        if args.lean:
            print(lean_source(data, args.positive_frequencies, observations + bracket, bracket), end="")
        else:
            result = {
                "positive_frequencies": args.positive_frequencies,
                "patches": len(data.weights),
                "density_of_states_per_mev": str(sum(data.weights)),
                "observations": [observation(*row) for row in observations],
            }
            if bracket:
                result["crossing_bracket"] = [observation(*row) for row in bracket]
                result["temperature_tolerance_met"] = bracket[1][0] - bracket[0][0] <= args.temperature_tolerance
            print(json.dumps(result, indent=2))
    except (OSError, ValueError, KeyError, TypeError, ZeroDivisionError) as error:
        parser.error(str(error))


if __name__ == "__main__":
    main()
