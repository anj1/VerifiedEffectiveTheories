#!/usr/bin/env python3
"""Assemble all occupations and certify the ground energies by full-matrix bisection."""
import argparse
from collections import Counter
from fractions import Fraction
import json
from math import ceil, floor

from certify import components, factor, hamiltonian, occupation_basis, solve_ones
from provenance import ARTIFACTS, SHELL_CANDIDATES, verify_shell_prediction

ENERGY_GRID = 10**34
OUTPUT_GRID = 10**18
WEIGHT_SCALE = 10**46
MATRIX_SCALE = 100


def load_design():
    """Pass only the frozen bare parameters to the assembler and solver."""
    verify_shell_prediction()
    data = json.loads((ARTIFACTS / "two_shell_prediction.json").read_text())
    d, g = Fraction(data["d"]), Fraction(data["g"])
    cases = [(case["r"], case["s"], tuple(map(int, case["sectors"]))) for case in data["cases"]]
    return d, g, cases


def positive_shift(block, shift):
    """Exact positive-definiteness test by fraction-free symmetric elimination."""
    size = len(block)
    work = [[v * ENERGY_GRID - (MATRIX_SCALE * shift if i == j else 0)
             for j, v in enumerate(row)] for i, row in enumerate(block)]
    last = 1
    for k in range(size):
        pivot = work[k][k]
        if pivot <= 0:
            return False
        for i in range(k + 1, size):
            for j in range(i, size):
                numerator = work[i][j] * pivot - work[k][i] * work[k][j]
                work[i][j], remainder = divmod(numerator, last)
                if remainder:
                    raise ArithmeticError("fraction-free elimination lost exact divisibility")
        last = pivot
    return True


def sector_certificate(matrix, codes, blocks):
    block_data = []
    for indices in blocks:
        block = [[matrix[i][j] for j in indices] for i in indices]
        floor_bound = min(map(sum, block))
        trial_bound = min(row[i] for i, row in enumerate(block))
        block_data.append((indices, block, floor_bound, trial_bound))
    threshold = min(entry[3] for entry in block_data)
    candidates = [(indices, block) for indices, block, lower, _ in block_data if lower <= threshold]
    left = (min(entry[2] for entry in block_data) - 1) * ENERGY_GRID // MATRIX_SCALE
    right = threshold * ENERGY_GRID // MATRIX_SCALE
    while right - left > 1:
        middle = (left + right) // 2
        if all(positive_shift(block, middle) for _, block in candidates):
            left = middle
        else:
            right = middle
    minima = [(indices, block) for indices, block in candidates if not positive_shift(block, right)]
    if len(minima) != 1:
        raise ArithmeticError("the minimum is not isolated to one component")
    indices, block = minima[0]

    # The shifted inverse is used only to produce a positive trial vector.
    # Exact componentwise Rayleigh ratios certify the rounded vector.
    relative_shift = Fraction((left - 1) * MATRIX_SCALE, ENERGY_GRID)
    weights = solve_ones(*factor(block, relative_shift))
    weights = [round(value * WEIGHT_SCALE / max(weights)) for value in weights]
    if min(weights) <= 0:
        raise ArithmeticError("expected a positive witness in the lowest component")
    ratios = [Fraction(sum(a * w for a, w in zip(row, weights)), MATRIX_SCALE * w)
              for row, w in zip(block, weights)]
    lo = Fraction(floor(min(ratios) * OUTPUT_GRID), OUTPUT_GRID)
    hi = Fraction(ceil(max(ratios) * OUTPUT_GRID), OUTPUT_GRID)
    if any(Fraction(bound, MATRIX_SCALE) < lo for ids, _, bound, _ in block_data if ids != indices):
        raise ArithmeticError("a different component requires its own lower certificate")
    return {
        "lo": str(lo), "hi": str(hi),
        "weights": [[codes[i], w] for i, w in zip(indices, weights)],
    }


def build_experiment():
    d, g, design = load_design()
    encoding = {"matrix_scale": MATRIX_SCALE, "off_diagonal_scaled": str(-g * MATRIX_SCALE)}
    bases = {}
    cases = []
    for r, s, sectors in design:
        levels = (-s, -r, -d, 0, d, r, s)
        results = {}
        for n in sectors:
            basis = occupation_basis(len(levels), n)
            codes = [sum(value * 3**i for i, value in enumerate(state)) for state in basis]
            rational_matrix = hamiltonian(levels, g, n)
            matrix = []
            for row in rational_matrix:
                scaled = [MATRIX_SCALE * entry for entry in row]
                if any(entry.denominator != 1 for entry in scaled):
                    raise ArithmeticError("matrix entry is outside the declared rational grid")
                matrix.append(list(map(int, scaled)))
            if any(value != matrix[j][i] or value not in (0, -g * MATRIX_SCALE)
                   for i, row in enumerate(matrix) for j, value in enumerate(row) if i != j):
                raise ArithmeticError("expected a symmetric matrix with uniform transfer amplitude")
            blocks = list(components(matrix))
            entries = [[i, j] for i, row in enumerate(matrix)
                       for j in range(i + 1, len(row)) if row[j]]
            record = {
                "dimension": len(codes), "occupation_codes": codes, "edges": entries,
                "component_sizes": sorted(Counter(map(len, blocks)).items()),
            }
            key = str(n)
            if key not in bases:
                bases[key] = record
            elif bases[key] != record:
                raise ArithmeticError("sparsity must be common to all four spectra")
            results[key] = {
                "diagonal_scaled": [row[i] for i, row in enumerate(matrix)],
                **sector_certificate(matrix, codes, blocks),
            }
        cases.append({
            "r": r, "s": s, "levels": list(map(str, levels)), "sectors": results,
        })
    contrast_lo = contrast_hi = Fraction(0)
    for case, sign in zip(cases, (1, -1, -1, 1), strict=True):
        sectors = case["sectors"]
        a, b, c = (sectors[str(n)] for n in (6, 7, 8))
        lo = Fraction(b["lo"]) - (Fraction(a["hi"]) + Fraction(c["hi"])) / 2
        hi = Fraction(b["hi"]) - (Fraction(a["lo"]) + Fraction(c["lo"])) / 2
        contrast_lo += lo if sign > 0 else -hi
        contrast_hi += hi if sign > 0 else -lo
    return {
        **encoding, "d": str(d), "g": str(g), "bases": bases, "cases": cases,
        "contrast": {"lo": str(contrast_lo), "hi": str(contrast_hi)},
    }


def lean_source(data):
    lines = [
        "/- Generated from exact bisection of the full occupation Hamiltonians. -/",
        "import Grain.ShellCertificate", "", "namespace Grain.TwoShell.FullSolve", "",
    ]
    for case in data["cases"]:
        r, s = case["r"], case["s"]
        for n, values in case["sectors"].items():
            name = f"r{r}s{s}n{n}"
            lines.extend([
                f"def {name} : ShellWitness where",
                f"  lo := {values['lo']}", f"  hi := {values['hi']}", "  weights := [",
            ])
            weights = [f"({code}, {weight})" for code, weight in values["weights"]]
            for i in range(0, len(weights), 2):
                lines.append("    " + ", ".join(weights[i:i + 2])
                             + ("," if i + 2 < len(weights) else "]"))
            lines.extend([
                "", "set_option maxHeartbeats 0 in", "set_option maxRecDepth 15000 in",
                f"theorem {name}Rows : ∀ c, checkRange {r} {s} {n} {name} c := by",
                "  intro c",
                "  fin_cases c <;> decide +kernel",
                "",
            ])
    lines += [
        "end Grain.TwoShell.FullSolve", "",
    ]
    return "\n".join(lines)


def json_artifact(data):
    # Sparse edge lists are compact, with one edge per row for readability.
    bases = {}
    for n, basis in data["bases"].items():
        edges = basis["edges"]
        bases[n] = {**basis, "edges": [i * basis["dimension"] + j for i, j in edges]}
    return json.dumps({**data, "bases": bases}, indent=2) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="regenerate without writing")
    args = parser.parse_args()
    paths = SHELL_CANDIDATES
    if not args.check and any(path.exists() for path in paths):
        raise ValueError("the full-solve records already exist")
    data = build_experiment()
    for path, content in zip(paths, (json_artifact(data), lean_source(data))):
        if args.check:
            if path.read_text() != content:
                raise ValueError(f"regeneration mismatch for {path.name}")
        else:
            with path.open("x") as output:
                output.write(content)
    for n, basis in data["bases"].items():
        print(f"N={n}: {basis['dimension']} states, {len(basis['edges'])} undirected transfers")
    for key, value in data["contrast"].items():
        print(key, float(Fraction(value)))


if __name__ == "__main__":
    main()
