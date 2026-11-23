#!/usr/bin/env python3
"""Predict a four-site response from one symmetry sector and validate in the site basis."""
import argparse
from fractions import Fraction as Q
from hashlib import sha256
import json
from pathlib import Path

from crystal_bcs import read_crystal
from dfpt_shell_eft import exact_ground
from fermion import add_scaled, assemble, connected_blocks, one_body, row_norm
from four_site_eft import (difference, momentum_interactions, pair_source_terms,
                           quantum_enclosure, shifted, site_models, vacuum_overlaps)
from thermal_bounds import exp_bounds, free_energy, log_bounds, rounded_bounds, trace_bounds

FULL_BASIS = range(256)
CHANNELS = ("cooper", "density", "exchange", "four_momenta")


def sector_key(state):
    momentum = imbalance = 0
    for k in range(4):
        up = (state >> (2*k)) & 1
        down = (state >> (2*k+1)) & 1
        if up != down:
            momentum ^= k
        imbalance += up-down
    return momentum, imbalance


ACTIVE = [state for state in FULL_BASIS if sector_key(state) == (0, 0)]
DISCARDED = [state for state in FULL_BASIS if sector_key(state) != (0, 0)]


def momentum_terms(crystal, hop):
    diagonal = crystal.hopping[0] - crystal.induced/2 - crystal.chemical_potential
    levels = [diagonal + hop*(xi-diagonal) for xi in crystal.xi]
    return one_body([(k, k, xi) for k, xi in enumerate(levels)])


def partition_envelope(matrix, t):
    # Jensen gives a lower bound from the diagonal. The quadratic form is
    # bounded below by diag(H_ii - sum_{j != i} |H_ij|) and by a lower
    # bound on each connected block's ground energy.
    lower = upper = Q(0)
    for states in connected_blocks(matrix):
        index = {i: j for j, i in enumerate(states)}
        block = [{index[j]: value for j, value in matrix[i].items()} for i in states]
        ground, _ = exact_ground(block, t/16)
        for i, row in enumerate(block):
            diagonal = row.get(i, 0)
            radius = sum(abs(value) for j, value in row.items() if j != i)
            lower += exp_bounds(-diagonal/t)[0]
            # Both bounds apply to each ordered eigenvalue by min-max.
            upper += exp_bounds(-max(ground, diagonal-radius)/t)[1]
    return lower, upper


def thermal_reduction(crystal, t, h, hop, source):
    terms = momentum_terms(crystal, hop) + momentum_interactions(crystal.coupling, 7)
    active = assemble(ACTIVE, terms)
    active_source = assemble(ACTIVE, pair_source_terms())
    z0 = trace_bounds(active, t)
    add_scaled(active, active_source, h*source)
    zh = trace_bounds(active, t)
    scale = 2*h**2
    response = difference(free_energy(z0, t), free_energy(zh, t), scale)

    discarded = assemble(DISCARDED, terms)
    discarded_source = assemble(DISCARDED, pair_source_terms())
    outside = partition_envelope(discarded, t)
    weight = outside[0]/z0[1], outside[1]/z0[0]
    source_exponent = h*source*row_norm(discarded_source)/t
    cosh_upper = (exp_bounds(source_exponent)[1] + exp_bounds(-source_exponent)[1])/2

    # For w = Z_D(0)/Z_A(0), R = Z_A(h)/Z_A(0), d = Z_D(h)/Z_D(0),
    # the ratio of full to active partition ratios is (1 + w*d/R)/(1+w).
    # Gauge symmetry and convexity give d >= 1. Golden–Thompson and the
    # same symmetry give d <= cosh(h ||S_D|| / t).
    ratio = zh[0]/z0[1], zh[1]/z0[0]
    lower = min((1+w/ratio[1])/(1+w) for w in weight)
    upper = max((1+w*cosh_upper/ratio[0])/(1+w) for w in weight)
    # The parent phonon estimate also needs an upper and lower bound on
    # the complete vacuum free energy at each source.
    add_scaled(discarded, discarded_source, h*source)
    discarded_h = partition_envelope(discarded, t)
    # Independent trace bounds can sharpen the ratio estimate, especially
    # when the field connects few of the thermally occupied states.
    lower = max(lower, (1 + discarded_h[0]/zh[1])/(1 + outside[1]/z0[0]))
    upper = min(upper, (1 + discarded_h[1]/zh[0])/(1 + outside[0]/z0[1]))
    error = t*log_bounds(lower)[0]/scale, t*log_bounds(upper)[1]/scale
    vacuum = [free_energy((z[0]+tail[0], z[1]+tail[1]), t)
              for z, tail in ((z0, outside), (zh, discarded_h))]
    return response, error, weight, vacuum


def add_intervals(left, right):
    return left[0]+right[0], left[1]+right[1]


def encode(interval):
    return list(map(str, rounded_bounds(*interval)))


def predict(crystal, t, h, omega):
    scale = 2*h**2
    bare, bare_error, bare_weight, _ = thermal_reduction(crystal, t, h, Q(1), Q(1))
    hop, source = vacuum_overlaps(crystal.induced, omega)
    dressed, dressed_error, dressed_weight, vacuum = thermal_reduction(crystal, t, h, hop[0], source[0])

    cooper_terms = momentum_interactions(crystal.coupling, 0)
    cooper = assemble(FULL_BASIS, momentum_terms(crystal, Q(1)) + cooper_terms)
    cooper_zero = free_energy(trace_bounds(cooper, t), t)
    add_scaled(cooper, assemble(FULL_BASIS, pair_source_terms()), h)
    cooper_response = difference(cooper_zero, free_energy(trace_bounds(cooper, t), t), scale)

    # For each nonzero displacement there are two disjoint site bonds per
    # spin. At most one hop per bond can act on a given configuration.
    ht = 4*sum(map(abs, crystal.hopping[1:]))
    one = crystal.hopping[0] - crystal.induced/2 - crystal.chemical_potential
    diagonal_norm = 4*max(abs(one), abs(2*one - 4*crystal.coupling))
    penalties = []
    overlap_errors = []
    for eta, (low, high) in zip((Q(0), h), vacuum, strict=True):
        st = 4*eta
        rounding = ht*(hop[1]-hop[0]) + st*(source[1]-source[0])
        quantum = quantum_enclosure((low-rounding, high+rounding), diagonal_norm, ht, st,
                                    hop, source, omega, t)
        penalties.append((quantum[0]-low, rounding))
        overlap_errors.append((-rounding, rounding))
    parent_error = add_intervals(dressed_error, difference(*penalties, scale))
    dressed_error = add_intervals(dressed_error, difference(*overlap_errors, scale))

    # Count the interaction monomials with a nonzero action in the retained
    # sector. Each channel is tested separately using its signed operators.
    channel_terms = [cooper_terms]
    channel_terms.extend([term for term in momentum_interactions(crystal.coupling, 1 << i)
                          if term not in cooper_terms] for i in range(3))
    surviving = {name: sum(any(assemble(ACTIVE, [(Q(1), ops)])) for _, ops in group)
                 for name, group in zip(CHANNELS, channel_terms, strict=True)}
    return {
        "retained_states": len(ACTIVE),
        "discarded_states": len(DISCARDED),
        "retained_interaction_monomials": surviving,
        "vacuum_hopping_overlap": encode(hop),
        "vacuum_source_overlap": encode(source),
        "discarded_to_retained_zero_source_partition_ratio": {
            "instantaneous": encode(bare_weight), "phonon_vacuum": encode(dressed_weight),
        },
        "response_per_site_per_mev": {
            "retained_instantaneous": encode(bare),
            "retained_phonon_vacuum": encode(dressed),
            "bare_cooper": encode(cooper_response),
            "full_instantaneous": encode(add_intervals(bare, bare_error)),
            "full_phonon_vacuum": encode(add_intervals(dressed, dressed_error)),
            "quantum_parent": encode(add_intervals(dressed, parent_error)),
        },
        "signed_error_per_site_per_mev": {
            "full_instantaneous_minus_retained": encode(bare_error),
            "full_phonon_vacuum_minus_retained": encode(dressed_error),
            "full_instantaneous_minus_bare_cooper": encode(
                add_intervals(difference(bare, cooper_response), bare_error)),
            "quantum_parent_minus_retained_phonon_vacuum": encode(parent_error),
        },
    }


def site_translation_orbits():
    remaining = {state for state in FULL_BASIS
                 if (state & 85).bit_count() == (state & 170).bit_count()}
    while remaining:
        representative = min(remaining)
        occupied = [slot for slot in range(8) if representative >> slot & 1]
        weights = {}
        for translation in range(4):
            slots = [slot ^ (2*translation) for slot in occupied]
            state = sum(1 << slot for slot in slots)
            inversions = sum(left > right for i, left in enumerate(slots) for right in slots[i+1:])
            weights[state] = weights.get(state, 0) + (-1)**inversions
        remaining.difference_update(weights)
        # The group average can vanish if a stabilizer acts with a minus sign.
        normalization = weights[representative]
        if normalization:
            yield representative, {i: Q(value, normalization) for i, value in weights.items()}


def site_invariant_block(matrix, orbits):
    # A translation-invariant vector is determined by its orbit representatives.
    # The rational orbit basis is unnormalized. Similarity preserves the trace.
    block = []
    for representative, _ in orbits:
        row = {}
        for j, (_, vector) in enumerate(orbits):
            value = sum(matrix[representative].get(state, 0)*weight
                        for state, weight in vector.items())
            if value:
                row[j] = value
        block.append(row)
    return block


def validate(crystal, prediction, t, h, omega):
    # Build in the site basis without the momentum vertices, momentum-state
    # selection, or discarded trace bounds used to make the prediction.
    diag, hopping, pair = site_models(crystal)
    # The two adjacent spin slots give net sign +1 for adding or removing
    # a local pair. Check the bare source directly, before dressing it.
    site_pairs = [{state ^ (3 << slot): Q(-1) for slot in range(0, 8, 2)
                   if ((state >> slot) & 3) in (0, 3)} for state in FULL_BASIS]
    if pair != site_pairs:
        raise ValueError("site source does not add and remove local pairs with the expected sign")
    orbits = list(site_translation_orbits())
    if len(orbits) != prediction["retained_states"]:
        raise ValueError("site translation projection disagrees with the retained dimension")

    def site_overlap(initial, final):
        displacement_sq = sum(
            (((final >> slot) & 3).bit_count() - ((initial >> slot) & 3).bit_count())**2
            for slot in range(0, 8, 2))
        return exp_bounds(-crystal.induced*displacement_sq/(4*omega))

    # A unit site hop is 1 -> 4 in the interleaved Fock basis, and a
    # local pair addition is 0 -> 3. All translates have the same overlap.
    hop, source = site_overlap(1, 4), site_overlap(0, 3)
    for name, bounds in (("vacuum_hopping_overlap", hop), ("vacuum_source_overlap", source)):
        if encode(bounds) != prediction[name]:
            raise ValueError(f"site displacement disagrees with the prediction for {name}")

    checks = {}
    retained_checks = {}
    errors = {}
    for name, hopping_scale, source_scale, retained, error in (
        ("full_instantaneous", (Q(1), Q(1)), (Q(1), Q(1)), "retained_instantaneous",
         "full_instantaneous_minus_retained"),
        ("full_phonon_vacuum", hop, source, "retained_phonon_vacuum",
         "full_phonon_vacuum_minus_retained"),
    ):
        zero = shifted(diag, hopping, pair, hopping_scale[0], 0)
        field = shifted(diag, hopping, pair, hopping_scale[0], h*source_scale[0])
        f0, fh = (free_energy(trace_bounds(matrix, t), t) for matrix in (zero, field))
        active_f0, active_fh = (free_energy(trace_bounds(site_invariant_block(matrix, orbits), t), t)
                               for matrix in (zero, field))
        active_response = difference(active_f0, active_fh, 2*h**2)
        predicted_active = tuple(map(Q, prediction["response_per_site_per_mev"][retained]))
        if max(active_response[0], predicted_active[0]) > min(active_response[1], predicted_active[1]):
            raise ValueError(f"site translation projection disagrees with the response for {retained}")
        retained_checks[retained] = encode(active_response)
        response = difference(f0, fh, 2*h**2)
        width = (2*row_norm(hopping)*(hopping_scale[1]-hopping_scale[0])
                 + h*row_norm(pair)*(source_scale[1]-source_scale[0])) / (2*h**2)
        response = add_intervals(response, (-width, width))
        checks[name] = response
        errors[error] = difference(response, active_response)
    errors["full_instantaneous_minus_bare_cooper"] = difference(
        checks["full_instantaneous"], tuple(map(Q, prediction["response_per_site_per_mev"]["bare_cooper"])))
    results = {"retained_site_basis_response_per_site_per_mev": retained_checks}
    for key, values in (("response_per_site_per_mev", checks), ("signed_error_per_site_per_mev", errors)):
        results[key] = {name: encode(interval) for name, interval in values.items()}
        for name, interval in results[key].items():
            lo, hi = map(Q, prediction[key][name])
            if not lo <= Q(interval[0]) <= Q(interval[1]) <= hi:
                raise ValueError(f"independent site-basis enclosure falls outside prediction for {name}")
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    prediction = commands.add_parser("predict")
    validation = commands.add_parser("validate")
    for command in (prediction, validation):
        command.add_argument("crystal", type=Path)
    prediction.add_argument("--at", type=Q, default=Q(1, 8), metavar="KBT_MEV")
    prediction.add_argument("--source", type=Q, default=Q(1, 20), metavar="MEV")
    prediction.add_argument("--phonon", type=Q, default=Q(512), metavar="MEV")
    validation.add_argument("prediction", type=Path)
    args = parser.parse_args()

    try:
        crystal = read_crystal(args.crystal, require_separated_levels=False)
        digest = sha256(args.crystal.read_bytes()).hexdigest()
        if args.command == "predict":
            t, h, omega = args.at, args.source, args.phonon
        else:
            saved = args.prediction.read_bytes()
            record = json.loads(saved)
            if record["crystal_sha256"] != digest:
                raise ValueError("crystal input differs from the retained prediction")
            t, h, omega = (Q(record[key]) for key in ("kbt_mev", "source_mev", "phonon_mev"))
        if len(crystal.hopping) != 4 or min(t, h, omega) <= 0:
            raise ValueError("expected four sites and positive temperature, source, and phonon energy")
        parameters = {"crystal_sha256": digest, "kbt_mev": str(t), "source_mev": str(h),
                      "phonon_mev": str(omega)}
        if args.command == "predict":
            result = parameters | predict(crystal, t, h, omega)
        else:
            result = parameters | {"prediction_sha256": sha256(saved).hexdigest()}
            result.update(validate(crystal, record, t, h, omega))
        print(json.dumps(result, indent=2))
    except (ArithmeticError, ValueError, KeyError, OSError) as error:
        parser.error(str(error))


if __name__ == "__main__":
    main()
