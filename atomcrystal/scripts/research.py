#!/usr/bin/env python3
"""Untrusted exact-arithmetic conjecture and witness generator.

Run `bulk` first. Freeze a prediction in artifacts/prediction.json before
running `slab`. Lean, not this program, checks all accepted scientific claims.
"""

import argparse
import json
from fractions import Fraction as Q


def as_text(x):
    return str(x.numerator) if x.denominator == 1 else f"{x.numerator}/{x.denominator}"


def solve(rows, rhs):
    """Rational Gaussian elimination; returns None if underdetermined/inconsistent."""
    a = [list(row) + [b] for row, b in zip(rows, rhs)]
    n = len(a[0]) - 1
    pivots = []
    rank = 0
    for col in range(n):
        pivot = next((j for j in range(rank, len(a)) if a[j][col]), None)
        if pivot is None:
            continue
        a[rank], a[pivot] = a[pivot], a[rank]
        d = a[rank][col]
        a[rank] = [v / d for v in a[rank]]
        for j in range(len(a)):
            if j != rank:
                scale = a[j][col]
                a[j] = [v - scale * w for v, w in zip(a[j], a[rank])]
        pivots.append(col)
        rank += 1
    if any(all(v == 0 for v in row[:n]) and row[n] != 0 for row in a):
        return None
    if rank < n:
        return None
    answer = [Q(0)] * n
    for j, col in enumerate(pivots):
        answer[col] = a[j][n]
    return answer


def bulk_response(s):
    # Generated from the declared two-ion Newton equation, not the fit law.
    mass_reduced, spring, ion_charge, cell_volume = Q(3), Q(6), Q(3), Q(1)
    field = Q(1)
    relative_displacement = ion_charge * field / (spring - mass_reduced * s)
    return ion_charge * relative_displacement / cell_volume


def rational_fit(samples, p_degree, q_degree):
    # y(s) * (1 + b1*s + ...) = a0 + a1*s + ...
    rows, rhs = [], []
    for s, y in samples:
        rows.append([s**j for j in range(p_degree + 1)] +
                    [-y * s**j for j in range(1, q_degree + 1)])
        rhs.append(y)
    coeff = solve(rows, rhs)
    if coeff is None:
        return None
    a = coeff[:p_degree + 1]
    b = [Q(1)] + coeff[p_degree + 1:]
    if not all(sum(a[j] * s**j for j in range(len(a))) ==
               y * sum(b[j] * s**j for j in range(len(b))) for s, y in samples):
        return None
    return a, b


def run_bulk():
    discovery_s = [Q(0), Q(1, 2), Q(1), Q(3, 2)]
    withheld_s = [Q(9, 4), Q(3), Q(7, 2), Q(4)]
    discovery = [(s, bulk_response(s)) for s in discovery_s]
    withheld = [(s, bulk_response(s)) for s in withheld_s]
    candidates = []
    for p_degree, q_degree in [(0, 0), (1, 0), (2, 0), (0, 1), (1, 1)]:
        fit = rational_fit(discovery, p_degree, q_degree)
        if fit is None:
            candidates.append({"degree": [p_degree, q_degree], "status": "rejected: discovery residual"})
            continue
        a, b = fit
        valid = all(sum(a[j] * s**j for j in range(len(a))) ==
                    y * sum(b[j] * s**j for j in range(len(b))) for s, y in withheld)
        candidates.append({"degree": [p_degree, q_degree],
                           "numerator": [as_text(v) for v in a],
                           "denominator": [as_text(v) for v in b],
                           "status": "withheld residual zero" if valid else "rejected: withheld residual"})
    result = {
        "classification": "empirical observation / hypothesis until the Lean bulk theorem",
        "model": "VerifiedPhysics.Base.Model: two ions, masses 6, charges +/-3, spring 6, reduced mass 3",
        "observable": "polarization / applied electric-field amplitude",
        "frequency_variable": "s = angular frequency squared, dimensionless",
        "discovery": [[as_text(s), as_text(y)] for s, y in discovery],
        "withheld": [[as_text(s), as_text(y)] for s, y in withheld],
        "candidates": candidates,
        "accepted_only_by": "VerifiedPhysics.exact_bulk_dielectric_law",
    }
    print(json.dumps(result, indent=2))


def run_slab(prediction_file):
    with open(prediction_file, encoding="utf-8") as file:
        prediction = json.load(file)
    assert prediction["status"] == "frozen higher-level prediction"
    s = Q(prediction["s_eff"])
    k2 = Q(prediction["k2"])
    # Matrix comes from the independently declared slab potential/Hessian.
    matrix = [[Q(2) + k2 / 3, -k2 / 3],
              [-k2 / 3, Q(2) + k2 / 2]]
    trace = matrix[0][0] + matrix[1][1]
    determinant = matrix[0][0] * matrix[1][1] - matrix[0][1] * matrix[1][0]
    def characteristic(t):
        return t*t - trace*t + determinant
    predicted_residual = characteristic(s)
    bracket = next(([Q(j, 100), Q(j+1, 100)] for j in range(1, 900)
                    if characteristic(Q(j, 100)) * characteristic(Q(j+1, 100)) < 0), None)
    if bracket is None:
        raise RuntimeError("no rational sign-change bracket found")
    result = {
        "classification": "untrusted certificate proposal; Lean checks it",
        "prediction_file": prediction_file,
        "geometry": "two ionic layers, open terminating boundary, dimensionless",
        "s_eff": as_text(s), "k2": as_text(k2),
        "operator": [[as_text(v) for v in row] for row in matrix],
        "characteristic_polynomial": f"t^2 - {as_text(trace)}*t + {as_text(determinant)}",
        "predicted_eigenvalue_residual": as_text(predicted_residual),
        "prediction_status": "rejected: exact predicted eigenvalue is not a slab eigenvalue" if predicted_residual else "exact match",
        "first_root_sign_change_bracket": [as_text(v) for v in bracket],
        "proposed_exact_first_root": "(9 - sqrt(17))/2",
        "proposed_eigenvector": ["2", "(sqrt(17)-1)/2"],
        "checked_by": ["VerifiedPhysics.certified_slab_mode",
                       "VerifiedPhysics.certified_slab_localization",
                       "VerifiedPhysics.verified_cross_scale_surface_prediction"],
    }
    print(json.dumps(result, indent=2))


def run_followup(prediction_file):
    with open(prediction_file, encoding="utf-8") as file:
        prediction = json.load(file)
    assert prediction["status"] == "frozen higher-level refined prediction"
    k2 = Q(prediction["new_k2"])
    lo, hi = map(Q, prediction["predicted_squared_frequency_interval"])
    matrix = [[Q(2) + k2 / 3, -k2 / 3],
              [-k2 / 3, Q(2) + k2 / 2]]
    trace = matrix[0][0] + matrix[1][1]
    determinant = matrix[0][0] * matrix[1][1] - matrix[0][1] * matrix[1][0]
    def characteristic(t):
        return t*t - trace*t + determinant
    lower_sign, upper_sign = characteristic(lo), characteristic(hi)
    result = {
        "classification": "untrusted lower-level certificate proposal",
        "prediction_file": prediction_file,
        "new_k2": as_text(k2),
        "operator": [[as_text(v) for v in row] for row in matrix],
        "characteristic_polynomial": f"t^2 - {as_text(trace)}*t + {as_text(determinant)}",
        "frozen_interval": [as_text(lo), as_text(hi)],
        "characteristic_at_lower_endpoint": as_text(lower_sign),
        "characteristic_at_upper_endpoint": as_text(upper_sign),
        "first_root_bracketed": 0 < lo < hi < trace / 2 and lower_sign * upper_sign < 0,
        "exact_eigenpair_to_check_in_Lean": ["7-sqrt(17)", "(2,(sqrt(17)-1)/2)"],
        "formal_check": "VerifiedPhysics.verified_refined_surface_prediction",
    }
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("stage", choices=["bulk", "slab", "followup"])
    parser.add_argument("--prediction", default="artifacts/prediction.json")
    args = parser.parse_args()
    if args.stage == "bulk":
        run_bulk()
    elif args.stage == "slab":
        run_slab(args.prediction)
    else:
        run_followup(args.prediction)
