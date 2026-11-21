#!/usr/bin/env python3
"""Compare four descriptions of the same four-site pair-source experiment."""
import argparse
from fractions import Fraction as Q
import json
from pathlib import Path

from crystal_bcs import read_crystal
from fermion import add_scaled, assemble, one_body, row_norm
from thermal_bounds import exp_bounds, free_energy, log_bounds, rounded_bounds, sqrt_bounds, trace_bounds


def difference(a, b, scale=1):
    return (a[0] - b[1]) / scale, (a[1] - b[0]) / scale


def models(crystal):
    states = range(256)
    diagonal = [(i, i, crystal.hopping[0] - crystal.induced/2 - crystal.chemical_potential)
                for i in range(4)]
    hopping = [(i, j, crystal.hopping[i ^ j]) for i in range(4) for j in range(4) if i != j]
    local = [(-(crystal.induced - crystal.repulsion),
              ((True, 2*i), (True, 2*i+1), (False, 2*i+1), (False, 2*i)))
             for i in range(4)]
    source = [(Q(-1), operators) for i in range(4) for operators in
              (((True, 2*i), (True, 2*i+1)), ((False, 2*i+1), (False, 2*i)))]
    cooper = [(-crystal.coupling,
               ((True, 2*i), (True, 2*i+1), (False, 2*j+1), (False, 2*j)))
              for i in range(4) for j in range(4)]
    band = [(i, i, xi) for i, xi in enumerate(crystal.xi)]
    return (assemble(states, one_body(diagonal) + local),
            assemble(states, one_body(hopping)), assemble(states, source),
            assemble(states, one_body(band) + cooper))


def shifted(diagonal, hopping, pair, hop_scale, source_scale):
    hamiltonian = [row.copy() for row in diagonal]
    add_scaled(hamiltonian, hopping, hop_scale)
    add_scaled(hamiltonian, pair, source_scale)
    return hamiltonian


def quantum_free_energy(diagonal, hopping, pair, eta, induced, omega, temperature):
    # After displacement every hopping/source term is an electronic
    # monomial times a unitary Weyl operator. Its vacuum expectation is
    # exp(-a) for a hop between two sites and exp(-2a) for an on-site pair.
    a = induced / (2*omega)
    hop = exp_bounds(-a)
    source = exp_bounds(-2*a)
    hamiltonian = shifted(diagonal, hopping, pair, hop[0], eta*source[0])
    ht = row_norm(hopping)
    st = eta * row_norm(pair)
    rounding = ht*(hop[1]-hop[0]) + st*(source[1]-source[0])
    vacuum = free_energy(trace_bounds(hamiltonian, temperature), temperature)
    # Each electronic transition has its own phonon displacement. The
    # triangle inequality row by row gives a block Schur norm bound.
    b = ht*sqrt_bounds(1-hop[0]**2)[1] + st*sqrt_bounds(1-source[0]**2)[1]
    v = row_norm(diagonal) + ht + st
    # Use the gap above the top of the vacuum block where available.
    # Smaller omega still yields valid, potentially wide, bounds.
    gap = max(omega/2, omega - 2*v - temperature)
    delta = b*b/gap
    q = exp_bounds(-omega/temperature)[1]
    tail = 1024 * exp_bounds((v+gap-omega)/temperature)[1] / (1-q)**4
    # Divide the upper trace by the certified vacuum trace before taking
    # logs. The partition function obeys Z <= exp(delta/t) Z_vac + tail.
    vacuum_inverse = exp_bounds((vacuum[1]+rounding)/temperature)[1]
    ratio = exp_bounds(delta/temperature)[1] + tail * vacuum_inverse
    return vacuum[0]-rounding-temperature*log_bounds(ratio)[1], vacuum[1]+rounding


def susceptibility_bounds(levels, gap, temperature):
    lo = hi = Q(0)
    for xi in levels:
        e0, e1 = sqrt_bounds(xi*xi + gap*gap)
        if e0 == 0:
            if e1 == 0:
                lo += 1/(4*temperature)
            else:
                lo += (1-exp_bounds(-e1/temperature)[1])/(2*e1*(1+exp_bounds(-e1/temperature)[1]))
            hi += 1/(4*temperature)
        else:
            q0 = exp_bounds(-e1/temperature)[1]
            q1 = exp_bounds(-e0/temperature)[0]
            lo += (1-q0)/(2*e1*(1+q0))
            hi += (1-q1)/(2*e0*(1+q1))
    return lo, hi


def mean_field_free_energy(levels, coupling, eta, t):
    if coupling <= 0:
        raise ValueError("the mean-field comparison requires an attractive channel")

    def side(x):
        if x == 0 and eta > 0:
            return 1
        lo, hi = susceptibility_bounds(levels, x, t)
        bias = eta/x if x else 0
        return 1 if coupling*lo+bias > 1 else -1 if coupling*hi+bias < 1 else 0

    low, high = Q(0), eta + len(levels)*coupling/2
    if eta == 0 and side(low) == -1:
        high = low
    else:
        while high-low > Q(1, 10**12):
            third = (high-low)/3
            left, right = low+third, high-third
            a, b = side(left), side(right)
            if a == 1:
                low = left
            if b == -1:
                high = right
            if a == -1:
                high = left
            if b == 1:
                low = right
            if a == b == 0:
                break
    # The cost is minimized at x >= eta. The band grand potential
    # decreases in x, so evaluate it at opposite bracket endpoints.
    low = max(eta, low)
    enclosures = []
    for x in (low, high):
        lo = hi = Q(0)
        for xi in levels:
            e0, e1 = sqrt_bounds(xi*xi+x*x)
            # xi - E - 2t log(1 + exp(-E/t)) decreases with E.
            # At fixed E the negative log term decreases with q = exp(-E/t).
            q_upper = exp_bounds(-e1/t)[1]
            q_lower = exp_bounds(-e0/t)[0]
            lo += xi-e1-2*t*log_bounds(1+q_upper)[1]
            hi += xi-e0-2*t*log_bounds(1+q_lower)[0]
        enclosures.append((lo, hi))
    return (low-eta)**2/coupling+enclosures[1][0], (high-eta)**2/coupling+enclosures[0][1]


def report(crystal, temperatures, field, frequencies):
    diag, hopping, pair, cooper = models(crystal)
    empty = [{} for _ in diag]
    experiments = []
    for t in temperatures:
        energies = {}
        for eta in (Q(0), field):
            energies[eta] = {
                "hubbard": free_energy(trace_bounds(shifted(diag, hopping, pair, 1, eta), t), t),
                "cooper": free_energy(trace_bounds(shifted(cooper, empty, pair, 1, eta), t), t),
                "bcs": mean_field_free_energy(crystal.xi, crystal.coupling, eta, t),
                **{f"phonon_{omega}": quantum_free_energy(diag, hopping, pair, eta, crystal.induced, omega, t)
                   for omega in frequencies},
            }
        # The number gauge rotation c -> i c makes F(-h) = F(h).
        response = {model: difference(value, energies[field][model], 2*field**2)
                    for model, value in energies[Q(0)].items()}
        discrepancies = {
            "cooper_minus_hubbard": difference(response["cooper"], response["hubbard"]),
            "bcs_minus_cooper": difference(response["bcs"], response["cooper"]),
            **{f"hubbard_minus_phonon_{omega}": difference(response["hubbard"], response[f"phonon_{omega}"])
               for omega in frequencies},
        }
        encode = lambda rows: {key: list(map(str, rounded_bounds(*value))) for key, value in rows.items()}
        experiments.append({"kbt_mev": str(t), "free_energy_at_zero_mev": encode(energies[Q(0)]),
                            "free_energy_at_source_mev": encode(energies[field]),
                            "response_per_site_per_mev": encode(response),
                            "reductions_per_site_per_mev": encode(discrepancies)})
    return {"source_mev": str(field), "phonon_energies_mev": list(map(str, frequencies)),
            "onsite_effective_mev": str(crystal.repulsion-crystal.induced),
            "cooper_attraction_mev": str(crystal.coupling), "temperatures": experiments}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("crystal", type=Path)
    parser.add_argument("--at", nargs="+", type=Q, default=[Q(1, 5), Q(1, 2)], metavar="KBT_MEV")
    parser.add_argument("--source", type=Q, default=Q(1, 20), metavar="MEV")
    parser.add_argument("--phonon", nargs="*", type=Q, default=[Q(32), Q(512)], metavar="MEV")
    args = parser.parse_args()
    try:
        crystal = read_crystal(args.crystal, require_separated_levels=False)
        if len(crystal.hopping) != 4 or min(args.source, *args.at, *args.phonon) <= 0:
            raise ValueError("expected four sites and positive temperatures, source, and phonon energies")
        print(json.dumps(report(crystal, args.at, args.source, args.phonon), indent=2))
    except (ArithmeticError, ValueError, KeyError, OSError) as error:
        parser.error(str(error))


if __name__ == "__main__":
    main()
