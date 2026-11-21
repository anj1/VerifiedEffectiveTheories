#!/usr/bin/env python3
"""Freeze DFPT shell predictions and compare them with full-sector enclosures."""
import argparse
from dataclasses import dataclass
from fractions import Fraction as Q
from hashlib import sha256
from itertools import product
import json
from math import floor, lcm
from pathlib import Path

from certify import factor
from dfpt_full_assembly import assemble_full_sector
from fermion import add_scaled, assemble, connected_blocks, one_body, row_norm, sector, square, submatrix, symmetric
from pairing import rational, shifted_factor
from thermal_bounds import sqrt_bounds

SOURCES = ("dfpt_shell_eft.py", "fermion.py", "certify.py", "thermal_bounds.py", "pairing.py")


@dataclass(frozen=True)
class Case:
    levels: tuple
    density: tuple
    scattering: tuple
    cartesian: tuple | None
    modes: tuple
    upstream: Q


def parse_case(data):
    levels = tuple(map(rational, data["levels_mev"]))
    if len(levels) < 2 or tuple(sorted(levels)) != levels:
        raise ValueError("levels must be in ascending energy order")
    n = len(levels)

    def orbital(i):
        if type(i) is not int or not 0 <= i < n:
            raise ValueError("orbital index out of bounds")
        return i

    def slot(i, spin):
        if spin not in (0, 1):
            raise ValueError("spin labels must be 0 or 1")
        return orbital(i), int(spin)

    if not data["screening_convention"]:
        raise ValueError("supply the interaction and DFPT screening convention")
    density = []
    for i, spin, j, other_spin, value in data["screened_density_terms"]:
        a, b = slot(i, spin), slot(j, other_spin)
        if a == b:
            raise ValueError("density interactions require distinct spin orbitals")
        density.append((a, b, rational(value)))
    # Each entry is the coefficient of exactly the written monomial. Supply
    # its Hermitian counterpart when distinct. A global check follows assembly.
    scattering = []
    for creation, annihilation, value in data["screened_scattering_terms"]:
        if len(creation) != 2 or len(annihilation) != 2:
            raise ValueError("a scattering term must create and annihilate two electrons")
        scattering.append((tuple(slot(*entry) for entry in creation),
                           tuple(slot(*entry) for entry in annihilation), rational(value)))

    def derivative(records):
        entries = {}
        for i, j, value in records:
            orbital(i)
            orbital(j)
            if i > j or (i, j) in entries:
                raise ValueError("provide each upper-triangle vertex entry once")
            entries[i, j] = rational(value)
        return entries

    cartesian = data.get("mass_weighted_cartesian_derivatives")
    if cartesian is not None:
        cartesian = tuple(derivative(records) for records in cartesian)
    modes = []
    for mode in data["mass_weighted_modes"]:
        force = rational(mode["omega_squared_mev2"])
        if force <= 0:
            raise ValueError("mass-weighted modes require positive squared frequencies")
        if cartesian is None:
            modes.append((force, derivative(mode["potential_derivative"])))
        else:
            if "potential_derivative" in mode:
                raise ValueError("provide either Cartesian or already projected derivatives")
            vector = tuple(map(rational, mode["eigenvector"]))
            if len(vector) != len(cartesian):
                raise ValueError("normal-mode and Cartesian derivative dimensions differ")
            if sum(v*v for v in vector) != 1 or any(
                sum(a*b for a, b in zip(vector, other, strict=True)) for _, other in modes
            ):
                raise ValueError("Cartesian mode vectors must describe an orthonormal stable subspace")
            modes.append((force, vector))
    error = rational(data["upstream_sector_error_mev"])
    if error < 0:
        raise ValueError("upstream error must be a nonnegative absolute bound")
    return Case(levels, tuple(density), tuple(scattering), cartesian, tuple(modes), error)


def frequency_lower(force):
    omega_lo = sqrt_bounds(force)[0]
    if not omega_lo:
        raise ValueError("frequency is below the enclosure's numerical resolution")
    return omega_lo


def electronic_sector(case, electrons):
    def spin_index(slot):
        orbital, spin = slot
        return 2*orbital + spin

    levels = case.levels
    direct = []
    for a, b, value in case.density:
        i, j = spin_index(a), spin_index(b)
        direct.append((value, ((True, i), (True, j), (False, j), (False, i))))
    for creation, annihilation, value in case.scattering:
        slots = map(spin_index, creation + annihilation)
        direct.append((value, tuple(zip((True, True, False, False), slots, strict=True))))

    states = sector(len(levels), electrons)
    kinetic = [sum(levels[j//2] for j in range(2*len(levels)) if a >> j & 1) for a in states]
    normal = assemble(states, direct + one_body([(i, i, v) for i, v in enumerate(levels)]))
    if not symmetric(normal):
        raise ValueError("screened electronic interaction is not Hermitian")
    matrix = [row.copy() for row in normal]
    dressing = Q(0)
    for force, mode in case.modes:
        if case.cartesian is None:
            derivative = mode
        else:
            derivative = {}
            for coefficient, entries in zip(mode, case.cartesian, strict=True):
                for key, value in entries.items():
                    derivative[key] = derivative.get(key, 0) + coefficient*value
        entries = [(i, j, value) for (i, j), value in derivative.items()]
        entries += [(j, i, value) for (i, j), value in derivative.items() if i != j]
        vertex = assemble(states, one_body(entries))
        # A = dH/dQ in mass-weighted normal coordinates. In oscillator
        # units the vertex is A/sqrt(2 omega) and its displacement is
        # A/sqrt(2 omega^3). Completing squares induces -A^2/(2 omega^2).
        add_scaled(matrix, square(vertex), -1/(2*force))
        dressing += row_norm(vertex)**2 / (2*force*frequency_lower(force))
    return states, kinetic, matrix, row_norm(normal), dressing


def form(matrix, vector):
    return sum((vector[i]*sum(v*vector[j] for j, v in row.items())
                for i, row in enumerate(matrix)), Q(0))


def ground_trial(matrix, upper):
    for indices in connected_blocks(matrix):
        block = submatrix(matrix, indices, indices)
        _, trial = shifted_factor([[-v for v in row] for row in block], [1]*len(block), -upper)
        if trial is not None:
            vector = [Q(0)]*len(matrix)
            for i, value in zip(indices, trial, strict=True):
                vector[i] = value
            return vector
    raise ArithmeticError("ground-energy endpoint did not yield a trial state")


def full_sector(case, electrons, tolerance):
    normal, modes, matrix = assemble_full_sector(case, electrons)
    if not symmetric(normal):
        raise ValueError("screened electronic interaction is not Hermitian")
    lo, hi = exact_ground(matrix, tolerance)
    trial = ground_trial(matrix, hi+tolerance)
    scale = 10**18 / max(map(abs, trial))
    trial = [round(v*scale) for v in trial]
    norm = sum(v*v for v in trial)
    electronic_energy = form(matrix, trial)/norm
    correction = Q(0)
    for force, vertex in modes:
        dressed = [sum(v*trial[j] for j, v in row.items()) for row in vertex]
        # This is the actual kinetic plus Coulomb form in the dressed
        # one-quantum trial, evaluated without a uniform vertex allowance.
        diff = form(normal, dressed) - electronic_energy*sum(v*v for v in dressed)
        correction += max(0, diff)/(2*force*frequency_lower(force)*norm)
    upstream = case.upstream
    return {"instantaneous": (lo, hi),
            "parent": (lo-upstream, electronic_energy+correction+upstream)}


def matrix_bounds(matrix):
    lower = min(row.get(i, 0)-sum(abs(v) for j, v in row.items() if i != j)
                for i, row in enumerate(matrix))
    upper = min(row.get(i, 0) for i, row in enumerate(matrix))
    return Q(lower), Q(upper)


def exact_ground(matrix, tolerance):
    """Full solve via exact fraction-free positive-definiteness tests."""
    lo, hi = matrix_bounds(matrix)
    for indices in connected_blocks(matrix):
        block = submatrix(matrix, indices, indices)
        left = min(row[i]-sum(abs(v) for j, v in enumerate(row) if j != i)
                   for i, row in enumerate(block))
        if left >= hi:
            continue
        right = min(hi, min(row[i] for i, row in enumerate(block)))
        scale = lcm(*(Q(v).denominator for row in block for v in row))
        integer = [[int(v*scale) for v in row] for row in block]
        while right-left > tolerance:
            mid = (left+right)/2
            if not positive_shift(integer, mid*scale):
                right = mid
            else:
                left = mid
        hi = min(hi, right)
    # Each component was either above the then-current upper endpoint
    # or bracketed to tolerance. Later components can only decrease hi.
    lo = max(lo, hi-tolerance)
    return lo, hi


def positive_shift(matrix, shift):
    """Test positive definiteness by symmetric fraction-free elimination."""
    n = len(matrix)
    work = [[v*shift.denominator - (shift.numerator if i == j else 0)
             for j, v in enumerate(row)] for i, row in enumerate(matrix)]
    previous = 1
    for k in range(n):
        pivot = work[k][k]
        if pivot <= 0:
            return False
        for i in range(k+1, n):
            for j in range(i, n):
                value = work[i][j]*pivot - work[k][i]*work[k][j]
                work[i][j], remainder = divmod(value, previous)
                if remainder:
                    raise ArithmeticError("fraction-free elimination lost exact divisibility")
        previous = pivot
    return True


def second_order(matrix, kinetic, tolerance):
    e0 = min(kinetic)
    reference = [i for i, v in enumerate(kinetic) if v == e0]
    output = []
    for i in reference:
        output.append({
            k: matrix[i].get(j, 0) -
            sum(value*matrix[b].get(j, 0)/(kinetic[b]-e0)
                for b, value in matrix[i].items() if kinetic[b] > e0)
            for k, j in enumerate(reference)
        })
    return exact_ground(output, tolerance)


def residual_reduction(a, b, d, delta, budget):
    """Form the lifted quadratic form and a Schur-complement error bound."""
    p = len(a)
    weights = [[Q(0)]*p for _ in d]
    scale = max(10**20, 10**6 * budget.denominator)
    diagonal = [row[i] for i, row in enumerate(d)]
    links = [[(j, v) for j, v in enumerate(row) if v] for row in d]
    step = 0
    while True:
        residual = [[b[j][i]+sum(v*weights[k][j] for k, v in links[i]) for j in range(p)]
                    for i in range(len(d))]
        error = sum((r*r for row in residual for r in row), Q(0))/delta
        if error <= budget:
            break
        step += 1
        if step == 128:
            raise ValueError("discarded inverse did not reach the requested resolution. Increase the active space")
        weights = [[Q(floor(scale*(w-r/diagonal[i])), scale) for w, r in zip(row, residual[i])]
                   for i, row in enumerate(weights)]
    lifted = [[a[i][j]+sum(b[i][k]*weights[k][j]+weights[k][i]*residual[k][j]
                           for k in range(len(d))) for j in range(p)] for i in range(p)]
    return lifted, error, step


def retained_ground(matrix, keep, tolerance):
    lo, hi = matrix_bounds(matrix)
    max_steps = 0
    # Since the matrix is block diagonal across its connected components,
    # Schur elimination only needs the components that can reach the trial energy.
    blocks = []
    for indices in connected_blocks(matrix):
        left = min(matrix[i].get(i, 0)-sum(abs(v) for j, v in matrix[i].items() if j != i)
                   for i in indices)
        if left >= hi:
            continue
        p = [i for i in indices if i in keep]
        q = [i for i in indices if i not in keep]
        a, b, d = (submatrix(matrix, rows, cols) for rows, cols in ((p, p), (p, q), (q, q)))
        if q:
            pivot_lower = min(row[i]-sum(abs(v) for j, v in enumerate(row) if i != j)
                              for i, row in enumerate(d))
            if pivot_lower <= hi:
                raise ValueError("discarded block is not certified above the ground window. Increase the active space")
        else:
            pivot_lower = None
        blocks.append((left, a, b, d, pivot_lower))
    budget = tolerance/4
    while hi-lo > tolerance:
        z = (hi+lo)/2
        all_lower = True
        upper = False
        largest_error = Q(0)
        for left, a, b, d, pivot_lower in blocks:
            if left >= z or not a:
                continue
            shifted_a = [[v-z if i == j else v for j, v in enumerate(row)] for i, row in enumerate(a)]
            shifted_d = [[v-z if i == j else v for j, v in enumerate(row)] for i, row in enumerate(d)]
            lifted, error, steps = residual_reduction(
                shifted_a, b, shifted_d, pivot_lower-z if d else 1, budget)
            max_steps = max(max_steps, steps)
            largest_error = max(largest_error, error)
            if factor(lifted, 0) is None:
                upper = True
                break
            if factor(lifted, error) is None:
                all_lower = False
        if upper:
            hi = z
        elif all_lower:
            lo = z
        else:
            lo, hi = max(lo, z-largest_error), min(hi, z+largest_error)
    return (lo, hi), max_steps


def keep_indices(states, levels, electrons, active):
    # Empty and full sectors have a single determinant and no Fermi window.
    if electrons in (0, 2*len(levels)):
        return set(range(len(states)))
    # Kinetic ground occupation supplies the Fermi rank. Include all ties
    # at the distance of the active-th orbital from the Fermi energy.
    mu = (levels[(electrons-1)//2] + levels[electrons//2])/2
    distance = sorted(abs(e-mu) for e in levels)[active-1]
    lower = [i for i, e in enumerate(levels) if e < mu-distance]
    upper = [i for i, e in enumerate(levels) if e > mu+distance]
    return {k for k, state in enumerate(states)
            if all((state >> (2*i)) & 3 == 3 for i in lower)
            and all((state >> (2*i)) & 3 == 0 for i in upper)}


def predicted_sector(case, electrons, active, tolerance):
    states, kinetic, matrix, normal_norm, dressing = electronic_sector(case, electrons)
    keep = keep_indices(states, case.levels, electrons, active)
    (lo, hi), steps = retained_ground(matrix, keep, tolerance)
    # Dressed-state variational bound versus the instantaneous ground energy.
    # The lower spectral bound applies to all oscillator occupations.
    phonon_error = (normal_norm-lo)*dressing
    upstream = case.upstream
    return {"instantaneous": (lo, hi), "parent": (lo-upstream, hi+phonon_error+upstream),
            "second_order": second_order(matrix, kinetic, tolerance),
            "phonon_error": phonon_error, "active_configurations": len(keep),
            "configurations": len(states), "max_jacobi_steps": steps}


def combine(terms):
    lo = hi = Q(0)
    for c, (a, b) in terms:
        lo += min(c*a, c*b)
        hi += max(c*a, c*b)
    return lo, hi


def load(path):
    data = json.loads(path.read_text(), parse_float=Q)
    cases = {key: parse_case(case) for key, case in data["cases"].items()}
    odd = data["odd_electrons"]
    active = data["active_orbitals"]
    if type(odd) is not int or not odd % 2 or any(not 1 <= odd < 2*len(c.levels) for c in cases.values()):
        raise ValueError("odd_electrons must be an interior odd particle number")
    if type(active) is not int or not cases or not 1 <= active <= min(len(c.levels) for c in cases.values()):
        raise ValueError("active_orbitals is outside the orbital basis")
    weights = {name: rational(weight) for name, weight in data["contrast_weights"].items()}
    if weights.keys() != cases.keys() or sum(weights.values()) or not any(weights.values()):
        raise ValueError("contrast weights must sum to zero across the declared cases")
    tolerance = rational(data["energy_resolution_mev"])
    if tolerance <= 0:
        raise ValueError("energy resolution must be positive")
    return cases, odd, active, weights, tolerance


def run(path, validate=False):
    cases, odd, active, weights, tol = load(path)
    coefficients = [(n, Q(1) if n == odd else -Q(1, 2)) for n in (odd-1, odd, odd+1)]
    sectors = {name: {str(n): full_sector(case, n, tol/32) if validate else
                     predicted_sector(case, n, active, tol) for n, _ in coefficients} for name, case in cases.items()}
    result = {"sectors": sectors}
    for quantity in (("instantaneous", "parent") if validate else ("instantaneous", "parent", "second_order")):
        result[quantity+"_contrast_mev"] = combine(
            (weights[key]*c, sectors[key][str(n)][quantity])
            for key, (n, c) in product(cases, coefficients))
    lo, hi = result["parent_contrast_mev"]
    result["parent_contrast_sign"] = "positive" if lo > 0 else "negative" if hi < 0 else "unresolved"
    return result


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def manifest(path):
    scripts = Path(__file__).resolve().parent
    return {"input_sha256": digest(path), "sources_sha256": {name: digest(scripts/name) for name in SOURCES}}


def canonical(data):
    return json.loads(json.dumps(data, default=str))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("predict", "freeze", "check", "validate"))
    parser.add_argument("input", type=Path)
    parser.add_argument("frozen", type=Path, nargs="?")
    args = parser.parse_args()
    try:
        if args.command == "predict":
            result = run(args.input)
        elif args.frozen is None:
            raise ValueError("supply the frozen prediction path")
        elif args.command == "freeze":
            result = {"manifest": manifest(args.input), "prediction": run(args.input)}
            with args.frozen.open("x") as file:
                json.dump(result, file, default=str, indent=2)
                file.write("\n")
        else:
            frozen = json.loads(args.frozen.read_text())
            if frozen["manifest"] != manifest(args.input):
                raise ValueError("frozen input or prediction code changed")
            if args.command == "check":
                if frozen["prediction"] != canonical(run(args.input)):
                    raise ValueError("prediction did not reproduce")
                result = {"prediction_reproduced": True}
            else:
                # The full solver consumes only the primitive export and
                # target resolution. Compare intervals after the full solve.
                result = run(args.input, validate=True)
                for case, sectors in result["sectors"].items():
                    for n, bounds in sectors.items():
                        for quantity, full in bounds.items():
                            predicted = tuple(map(Q, frozen["prediction"]["sectors"][case][n][quantity]))
                            if max(full[0], predicted[0]) > min(full[1], predicted[1]):
                                raise ArithmeticError(f"{quantity} enclosures disagree in {case}, N={n}")
                for quantity in ("instantaneous", "parent"):
                    predicted = list(map(Q, frozen["prediction"][quantity+"_contrast_mev"]))
                    full = result[quantity+"_contrast_mev"]
                    result[quantity+"_contrast_contained"] = predicted[0] <= full[0] <= full[1] <= predicted[1]
        print(json.dumps(result, default=str, indent=2))
    except (ArithmeticError, ValueError, KeyError, TypeError, OSError) as error:
        parser.error(str(error))


if __name__ == "__main__":
    main()
