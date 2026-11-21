#!/usr/bin/env python3
"""Check virtual phonon exchange in the full spinful occupation sectors."""
import argparse
from collections import defaultdict
from fractions import Fraction
from itertools import combinations
import json

from provenance import ARTIFACTS, verify_shell_prediction

ORBITALS = 7
BONDS = tuple(combinations(range(ORBITALS), 2))
ALPHA = Fraction(1, 10**8)
OMEGA = 5 * 10**13
OUTPUT = ARTIFACTS / "phonon_bridge.json"
SCALE = 200  # energies in 1/200 of a central spacing


def spin_basis(electrons):
    return [sum(1 << k for k in occupied) for occupied in combinations(range(2 * ORBITALS), electrons)]


def counts(state):
    return tuple(((state >> (2 * i)) & 3).bit_count() for i in range(ORBITALS))


def code(state):
    return sum(value * 3**i for i, value in enumerate(counts(state)))


def bond_row(state, bond):
    """Two spin-conserving one-electron moves in a site-ordered Fock basis."""
    i, j = bond
    for spin in (0, 1):
        lo, hi = 2 * i + spin, 2 * j + spin
        endpoints = (1 << lo) | (1 << hi)
        occupied = state & endpoints
        if occupied in (1 << lo, 1 << hi):
            between = ((1 << hi) - 1) ^ ((1 << (lo + 1)) - 1)
            sign = 1 - 2 * ((state & between).bit_count() % 2)
            yield state ^ endpoints, sign


def square_rows(states):
    """Rows of the sum of all bond and local density vertex squares."""
    square = {}
    bonds = {bond: {x: tuple(bond_row(x, bond)) for x in states} for bond in BONDS}
    if any((x, sign) not in matrix[y] for matrix in bonds.values()
           for x, row in matrix.items() for y, sign in row):
        raise ArithmeticError("expected symmetric one-electron vertices")
    for x in states:
        row = defaultdict(int)
        row[x] = sum(n*n for n in counts(x))
        for matrix in bonds.values():
            for y, a in matrix[x]:
                for z, b in matrix[y]:
                    row[z] += a*b
        square[x] = {z: v for z, v in row.items() if v}
    return square, bonds


def active_component(state, electrons):
    singles = tuple(i for i, n in enumerate(counts(state)) if n == 1)
    if electrons == 7 and singles == (3,):
        return (state >> 6) & 3
    if electrons != 7 and not singles:
        return 0
    return None


def bcs_pattern(base, diagonal, off_diag):
    size = base["dimension"]
    codes = base["occupation_codes"]
    rows = {a: {a: value} for a, value in zip(codes, diagonal)}
    for edge in base["edges"]:
        i, j = divmod(edge, size)
        rows[codes[i]][codes[j]] = off_diag
        rows[codes[j]][codes[i]] = off_diag
    return rows


def compare_electronic_model(states, square, levels, base, certificate, electrons):
    kinetic = {x: sum(n * level for n, level in zip(counts(x), levels)) for x in states}
    active = {x: active_component(x, electrons) for x in states}
    by_code = {(active[x], code(x)): x for x in states if active[x] is not None}
    reduced = bcs_pattern(base, certificate["diagonal_scaled"], -1)
    active_codes = {a for _, a in by_code}
    for a, row in reduced.items():
        if any((a in active_codes) != (b in active_codes) for b in row):
            raise ArithmeticError("mixed active and complementary rows in the reduced matrix")
        if a not in active_codes:
            bound = row[a] - sum(abs(value) for b, value in row.items() if b != a)
            if Fraction(bound, 100) <= Fraction(certificate["hi"]):
                raise ArithmeticError("a different reduced-BCS block can compete for the minimum")
    offset_scaled = -(24 + electrons)
    complement_lower = None
    for x in states:
        row = {y: -value for y, value in square[x].items()}
        row[x] = row.get(x, 0) + SCALE * kinetic[x]
        if active[x] is None:
            if any(value and active[y] is not None for y, value in row.items()):
                raise ArithmeticError("the high electronic sector couples to an active block")
            low = row[x] - sum(abs(value) for y, value in row.items() if y != x)
            complement_lower = low if complement_lower is None else min(low, complement_lower)
        else:
            expected = {by_code[(active[x], b)]: 2*value
                        for b, value in reduced[code(x)].items()
                        if (active[x], b) in by_code}
            expected[x] += offset_scaled
            if {y: value for y, value in row.items() if value} != {
                    y: value for y, value in expected.items() if value}:
                raise ArithmeticError("the induced electronic matrix disagrees with reduced BCS")
    offset = Fraction(offset_scaled, SCALE)
    lower = Fraction(certificate["lo"]) + offset
    upper = Fraction(certificate["hi"]) + offset
    complement_lower = Fraction(complement_lower, SCALE)
    if complement_lower <= upper:
        raise ArithmeticError("a high electronic block can compete for the minimum")
    return kinetic, by_code, offset, lower, upper, complement_lower


def dressed_trial(kinetic, bonds, by_code, certificate, electrons):
    """Expectation of the primitive Hamiltonian on a vacuum plus one-phonon trial."""
    spin = 1 if electrons == 7 else 0
    vector = {by_code[(spin, a)]: w for a, w in certificate["weights"]}
    weights_sq = sum(w*w for w in vector.values())
    kinetic_numerator = sum(kinetic[x]*w*w for x, w in vector.items())
    # Local density vertices are diagonal in the occupation basis.
    vertex_sq = sum(sum(n*n for n in counts(x))*w*w for x, w in vector.items())
    dressed_kinetic = sum(kinetic[x]*sum(n*n for n in counts(x))*w*w for x, w in vector.items())
    for matrix in bonds.values():
        y = defaultdict(int)
        for state, w in vector.items():
            for target, sign in matrix[state]:
                y[target] += sign*w
        vertex_sq += sum(w*w for w in y.values())
        dressed_kinetic += sum(kinetic[state]*w*w for state, w in y.items())
    # Nonzero ladder matrix elements are the vacuum-to-one elements.
    numerator = kinetic_numerator - OMEGA * ALPHA**2 * vertex_sq + ALPHA**2 * dressed_kinetic
    return numerator / (weights_sq + ALPHA**2 * vertex_sq)


def outward(value, upper=False):
    grid = 10**20
    z = value * grid
    integer = -((-z.numerator)//z.denominator) if upper else z.numerator//z.denominator
    return Fraction(integer, grid)


def build():
    verify_shell_prediction()
    source = json.loads((ARTIFACTS / "two_shell_full_solve.json").read_text())
    g = Fraction(source["g"])
    if source["matrix_scale"] != 100 or Fraction(source["d"]) != 1:
        raise ValueError("expected the frozen seven-orbital spacing units")
    if OMEGA*ALPHA**2 != g/2 or Fraction(source["off_diagonal_scaled"]) != -1:
        raise ValueError("the harmonic parameters must reproduce the frozen coupling")
    matrices = {}
    for n in (6, 7, 8):
        states = spin_basis(n)
        matrices[n] = (states, *square_rows(states))
    cases = []
    contrasts = []
    for case in source["cases"]:
        values = {}
        levels = list(map(Fraction, case["levels"]))
        for n, (states, square, bonds) in matrices.items():
            base = source["bases"][str(n)]
            certificate = case["sectors"][str(n)]
            kinetic, by_code, offset, lo, hi, high = compare_electronic_model(
                states, square, levels, base, certificate, n)
            trial = outward(dressed_trial(kinetic, bonds, by_code, certificate, n), upper=True)
            if not lo <= trial <= hi + Fraction(2, 10**12):
                raise ArithmeticError("dressed trial did not meet its energy budget")
            values[str(n)] = {
                "spinful_dimension": len(states),
                "active_dimensions": [sum(spin == component for spin, _ in by_code)
                                      for component in sorted({spin for spin, _ in by_code})],
                "electronic_offset": str(offset),
                "complement_lower": str(high),
                "electronic_lo": str(lo), "electronic_hi": str(hi),
                "microscopic_lo": str(lo), "microscopic_hi": str(trial),
            }
        a, b, c = (values[str(n)] for n in (6, 7, 8))
        lo = Fraction(b["microscopic_lo"]) - (Fraction(a["microscopic_hi"]) + Fraction(c["microscopic_hi"]))/2
        hi = Fraction(b["microscopic_hi"]) - (Fraction(a["microscopic_lo"]) + Fraction(c["microscopic_lo"]))/2
        contrasts.append((lo, hi))
        cases.append({"r": case["r"], "s": case["s"], "sectors": values})
    (la, ua), (lb, ub), (lc, uc), (ld, ud) = contrasts
    lo, hi = la - ub - uc + ld, ua - lb - lc + ud
    frozen = json.loads((ARTIFACTS / "two_shell_prediction.json").read_text())["contrast"]
    if not 0 < Fraction(frozen["lo"]) <= lo <= hi <= Fraction(frozen["hi"]):
        raise ArithmeticError("microscopic contrast falls outside the frozen window")
    return {
        "phonon_frequency": OMEGA, "vertex_over_frequency": str(ALPHA),
        "bond_modes": len(BONDS), "density_modes": ORBITALS,
        "cases": cases, "contrast": {"lo": str(lo), "hi": str(hi)},
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="regenerate without writing")
    args = parser.parse_args()
    result = build()
    content = json.dumps(result, indent=2) + "\n"
    if args.check:
        if OUTPUT.read_text() != content:
            raise ValueError("phonon bridge regeneration mismatch")
    else:
        with OUTPUT.open("x") as file:
            file.write(content)
    print("Microscopic contrast enclosure")
    for key, value in result["contrast"].items():
        print(key, float(Fraction(value)))


if __name__ == "__main__":
    main()
