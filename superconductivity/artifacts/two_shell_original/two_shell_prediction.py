#!/usr/bin/env python3
"""Build a two-step Schur approximation and certify its lifted residuals.

The predictor uses only finite Jacobi sums and a final scalar root search.
Arithmetic used to enclose the sector energies is exact.
"""
import argparse
from decimal import Decimal, localcontext
from fractions import Fraction
from itertools import combinations, product
import json
from math import ceil, floor
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
G = Fraction(1, 100)
RADII = tuple(product((2, 5), (6, 14)))
SECTORS = (6, 7, 8)
TERMS = 8
ENERGY_GRID = 10**17
WEIGHT_SCALE = 10**24


def schur_prefix(matrix, retain):
    """Return the approximate Schur matrix and the map lifting its vectors."""
    discard = [i for i in matrix if i not in retain]
    lift = {i: {} for i in discard}
    reduced = {i: {} for i in retain}
    links = {i: [k for k in discard if k != i and matrix[i][k]] for i in discard}
    if any(matrix[i][i] <= 0 or
           sum(abs(matrix[i][k]) for k in links[i]) >= matrix[i][i] for i in discard):
        raise ArithmeticError("Jacobi expansion needs a positive, dominant pivot")
    for j in retain:
        term = {i: -matrix[i][j] / matrix[i][i] for i in discard}
        total = term.copy()
        for _ in range(TERMS - 1):
            term = {i: -sum(matrix[i][k] * term[k] for k in links[i]) / matrix[i][i]
                    for i in discard}
            total = {i: total[i] + term[i] for i in discard}
        for i in discard:
            lift[i][j] = total[i]
        for i in retain:
            reduced[i][j] = matrix[i][j] + sum(matrix[i][k] * total[k] for k in discard)
    return reduced, lift


def central_response(matrix, ref):
    """Exactly eliminate the one or two excited central configurations."""
    discarded = [i for i in matrix if i != ref]
    i = discarded[0]
    if len(discarded) == 1:
        tail = {i: -matrix[i][ref] / matrix[i][i]}
    elif len(discarded) == 2:
        j = discarded[1]
        det = matrix[i][i] * matrix[j][j] - matrix[i][j] * matrix[j][i]
        tail = {
            i: (-matrix[j][j] * matrix[i][ref] + matrix[i][j] * matrix[j][ref]) / det,
            j: (-matrix[i][i] * matrix[j][ref] + matrix[j][i] * matrix[i][ref]) / det,
        }
    else:
        raise ValueError("expected two or three central configurations")
    value = matrix[ref][ref] + sum(matrix[ref][i] * x for i, x in tail.items())
    return value, {ref: Decimal(1), **tail}


def predict_sector(r, s, electrons):
    levels = (-s, -r, -1, 0, 1, r, s)
    allowed = [i for i in range(7) if electrons != 7 or i != 3]
    pairs = electrons // 2
    states = list(map(frozenset, combinations(allowed, pairs)))
    neighbors = [[j for j, b in enumerate(states) if len(a ^ b) == 2] for a in states]
    diagonal = [2 * sum(levels[i] for i in a) - G * pairs for a in states]
    retain_outer = [i for i, a in enumerate(states) if 0 in a and 6 not in a]
    retain_inner = [i for i in retain_outer if 1 in states[i] and 5 not in states[i]]
    ref = min(range(len(diagonal)), key=diagonal.__getitem__)

    g = Decimal(G.numerator) / Decimal(G.denominator)
    onsite = [Decimal(v.numerator) / Decimal(v.denominator) for v in diagonal]

    def evaluate(z):
        matrix = {i: {j: onsite[i] - z if i == j else -g if j in row else Decimal(0)
                      for j in range(len(states))}
                  for i, row in enumerate(neighbors)}
        middle, outer_lift = schur_prefix(matrix, retain_outer)
        central, inner_lift = schur_prefix(middle, retain_inner)
        value, vector = central_response(central, ref)
        return value, vector, inner_lift, outer_lift

    left, right = onsite[ref] - 12 * g, onsite[ref]
    if not evaluate(left)[0] > 0 > evaluate(right)[0]:
        raise ArithmeticError("central response fails to bracket zero")
    for _ in range(65):
        mid = (left + right) / 2
        if evaluate(mid)[0] > 0:
            left = mid
        else:
            right = mid
    z = (left + right) / 2
    _, vector, inner_lift, outer_lift = evaluate(z)
    for lift in (inner_lift, outer_lift):
        vector.update({i: sum(value * vector[j] for j, value in row.items())
                       for i, row in lift.items()})
    weights = [round(vector[i] * WEIGHT_SCALE) for i in range(len(states))]
    if min(weights) <= 0:
        raise ArithmeticError("expected strictly positive amplitudes in the active block")
    ratios = [a - G * Fraction(sum(weights[j] for j in row), weights[i])
              for i, (a, row) in enumerate(zip(diagonal, neighbors))]
    lo = Fraction(floor(min(ratios) * ENERGY_GRID), ENERGY_GRID)
    hi = Fraction(ceil(max(ratios) * ENERGY_GRID), ENERGY_GRID)
    center = Fraction(round(z * ENERGY_GRID), ENERGY_GRID)
    if max(abs(lo - center), abs(hi - center)) > Fraction(1, 10**12):
        raise ArithmeticError("sector error exceeded its budget")
    encoded = [(sum(2 * 3**i for i in a) + (27 if electrons == 7 else 0), w)
               for a, w in zip(states, weights)]
    return {
        "center": str(center), "lo": str(lo), "hi": str(hi),
        "dimensions": [len(states), len(retain_outer), len(retain_inner)],
        "weights": sorted(encoded),
    }


def parity(sectors):
    even, odd, next_even = (sectors[str(n)] for n in SECTORS)
    energy = lambda row, key: Fraction(row[key])
    return {
        "center": energy(odd, "center") - (energy(even, "center") + energy(next_even, "center")) / 2,
        "lo": energy(odd, "lo") - (energy(even, "hi") + energy(next_even, "hi")) / 2,
        "hi": energy(odd, "hi") - (energy(even, "lo") + energy(next_even, "lo")) / 2,
    }


def build_prediction():
    with localcontext(prec=48):
        cases = [{
            "r": r, "s": s,
            "sectors": {str(n): predict_sector(r, s, n) for n in SECTORS},
        } for r, s in RADII]
    a, b, c, d = [parity(case["sectors"]) for case in cases]
    contrast = {
        "center": str(a["center"] - b["center"] - c["center"] + d["center"]),
        "lo": str(a["lo"] - b["hi"] - c["hi"] + d["lo"]),
        "hi": str(a["hi"] - b["lo"] - c["lo"] + d["hi"]),
    }
    if Fraction(contrast["lo"]) <= 0:
        raise ArithmeticError("mixed contrast does not exclude zero")
    return {"d": 1, "g": str(G), "neumann_terms": TERMS, "cases": cases, "contrast": contrast}


def scalar_control():
    """Enclose the contrast for the inverse-coupling update on three orbitals."""
    from certify import components, factor, hamiltonian

    def bounds(strength, electrons):
        matrix = hamiltonian((-1, 0, 1), strength, electrons)
        blocks = [[[matrix[i][j] for j in part] for i in part] for part in components(matrix)]
        lo = floor(min(map(sum, matrix)) * ENERGY_GRID) - 1
        hi = ceil(min(row[i] for i, row in enumerate(matrix)) * ENERGY_GRID)
        while hi - lo > 1:
            mid = (lo + hi) // 2
            if all(factor(block, Fraction(mid, ENERGY_GRID)) is not None for block in blocks):
                lo = mid
            else:
                hi = mid
        return Fraction(lo, ENERGY_GRID), Fraction(hi, ENERGY_GRID)

    intervals = []
    for r, s in RADII:
        strength = 1 / (1 / G - Fraction(1, r) - Fraction(1, s))
        (l2, u2), (l3, u3), (l4, u4) = (bounds(strength, n) for n in (2, 3, 4))
        intervals.append((l3 - (u2 + u4) / 2, u3 - (l2 + l4) / 2))
    (la, ua), (lb, ub), (lc, uc), (ld, ud) = intervals
    return la - ub - uc + ld, ua - lb - lc + ud


def lean_source(data):
    lines = [
        "/- Generated by scripts/two_shell_prediction.py from nested Schur approximants. -/",
        "import Grain.ShellCertificate", "", "namespace Grain.TwoShell.Prediction", "",
    ]
    for case in data["cases"]:
        r, s = case["r"], case["s"]
        for n, values in case["sectors"].items():
            name = f"r{r}s{s}n{n}"
            lines += [
                f"def {name}Center : ℚ := {values['center']}",
                f"def {name} : ShellWitness where",
                f"  lo := {values['lo']}", f"  hi := {values['hi']}",
                "  weights := [",
            ]
            weights = [f"({code}, {weight})" for code, weight in values["weights"]]
            lines += [
                "    " + ", ".join(weights[i:i + 2]) + ("," if i + 2 < len(weights) else "]")
                for i in range(0, len(weights), 2)
            ]
            lines += [
                "", "set_option maxHeartbeats 0 in", "set_option maxRecDepth 15000 in",
                f"theorem {name}Rows : ∀ c, checkRange {r} {s} {n} {name} c := by",
                "  intro c",
                "  fin_cases c <;> decide +kernel",
                "",
            ]
    return "\n".join(lines + ["end Grain.TwoShell.Prediction", ""])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--check", action="store_true", help="reproduce without writing")
    mode.add_argument("--scalar-control", action="store_true", help="enclose the scalar coupling control")
    args = parser.parse_args()
    if args.scalar_control:
        lo, hi = scalar_control()
        print(f"Scalar contrast interval [{lo}, {hi}]")
        return
    paths = [ROOT / "artifacts" / "two_shell_prediction.json", ROOT / "Grain" / "ShellPredictionData.lean"]
    if not args.check and any(path.exists() for path in paths):
        raise ValueError("prediction files already exist")
    data = build_prediction()
    outputs = [json.dumps(data, indent=2) + "\n", lean_source(data)]
    for path, content in zip(paths, outputs):
        if args.check:
            if path.read_text() != content:
                raise ValueError(f"regeneration mismatch for {path.name}")
        else:
            with path.open("x") as output:
                output.write(content)
    print("Two-shell prediction reproduced" if args.check else "Two-shell prediction generated")
    for key, value in data["contrast"].items():
        print(key, float(Fraction(value)))


if __name__ == "__main__":
    main()
