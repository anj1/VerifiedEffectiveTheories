"""Conservative rational finite-sample bounds on covariance Binder slopes.

This diagnostic may be unresolved. It never replaces the exploratory
bootstrap with a falsely certified exponent. The external empirical-Bernstein
theorem and ideal iid CFTP stream law remain explicit premises.
"""
import hashlib
import json
import math
from fractions import Fraction as F
from pathlib import Path

from prg_covcert import ROOT, RAW, enc, sqrt_upper

RESULT = ROOT / "grandcanonical_results"
OUT = RESULT / "prg_slope_bounds.json"
LOG_UPPER = F(7)


def interval(values, lower, upper):
    n = len(values)
    assert n > 1 and all(lower <= x <= upper for x in values)
    mean = sum(values, F(0)) / n
    variance = (sum((x * x for x in values), F(0)) - n * mean * mean) / (n - 1)
    assert variance >= 0
    span = upper - lower
    radius = sqrt_upper(2 * variance * LOG_UPPER / n) + \
        7 * LOG_UPPER * span / (3 * (n - 1))
    return max(lower, mean - radius), min(upper, mean + radius), mean, variance, radius


def add(a, b):
    return a[0] + b[0], a[1] + b[1]


def neg(a):
    return -a[1], -a[0]


def mul(a, b):
    p = [x * y for x in a for y in b]
    return min(p), max(p)


def div(a, b):
    assert b[0] > 0
    return mul(a, (1 / b[1], 1 / b[0]))


def abs_interval(a):
    if a[0] > 0:
        return a
    if a[1] < 0:
        return -a[1], -a[0]
    return None


def load(L, r, n, stage):
    a, b = r.numerator, r.denominator
    path = RAW / f"cftp_stage{stage}_quot_L{L}_r{a}_{b}_n{n}.jsonl"
    rows = [json.loads(line) for line in path.read_text().splitlines()]
    assert len(rows) == n and len({z["seed"] for z in rows}) == n
    assert all(z["success"] and z["L"] == L and
               z["r_num"] == a and z["r_den"] == b and
               z["algorithm"] == "cftp" for z in rows)
    V, E = L ** 3, 3 * L ** 3
    X = [F(z["magnetization_sum_2"], V ** 2) for z in rows]
    Y = [x * x for x in X]
    D = [F(z["disagreement_count"]) for z in rows]
    specs = {"m2": (X, F(0), F(1)),
             "m4": (Y, F(0), F(1)),
             "D": (D, F(0), F(E)),
             "m2_D": ([x * d for x, d in zip(X, D)], F(0), F(E)),
             "m4_D": ([y * d for y, d in zip(Y, D)], F(0), F(E))}
    bounds, diagnostics = {}, {}
    for name, (values, lower, upper) in specs.items():
        lo, hi, mean, var, radius = interval(values, lower, upper)
        bounds[name] = (lo, hi)
        diagnostics[name] = {"mean": enc(mean), "interval": [enc(lo), enc(hi)],
                             "sample_variance": enc(var), "radius": enc(radius)}
    aa, bb, dd, p, q = [bounds[k] for k in ("m2", "m4", "D", "m2_D", "m4_D")]
    a_prime = add(p, neg(mul(aa, dd)))
    b_prime = add(q, neg(mul(bb, dd)))
    slope = None
    if aa[0] > 0:
        first = neg(div(b_prime, mul((F(3), F(3)), mul(aa, aa))))
        second = div(mul((F(2), F(2)), mul(bb, a_prime)),
                     mul((F(3), F(3)), mul(mul(aa, aa), aa)))
        slope = add(first, second)
    return {"L": L, "r": [a, b], "n": n, "stage": stage,
            "raw_file": str(path.relative_to(ROOT)),
            "raw_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "five_mean_bounds": diagnostics,
            "cov_m2_D_interval": [enc(x) for x in a_prime],
            "cov_m4_D_interval": [enc(x) for x in b_prime],
            "conditional_95_familywise_slope_interval": [enc(x) for x in slope] if slope else None}, slope


def main():
    assert sum((F(7) ** k / math.factorial(k) for k in range(12)), F(0)) > 800
    design_path = RESULT / "prg_slope_bounds_design.json"
    selection = json.loads((RESULT / "prg_stage5_selection.json").read_text())
    r8 = F(*selection["selected_r"])
    cells, slopes = {}, {}
    for L, r, n, stage in ((4, F(16, 25), 30000, 4),
                           (6, F(16, 25), 30000, 4),
                           (8, r8, 12000, 5),
                           (12, r8, 12000, 5)):
        cells[str(L)], slopes[L] = load(L, r, n, stage)
        print("bounded slope cell", L, flush=True)
    quotients = {}
    for small, large in ((4, 6), (8, 12)):
        lhs = abs_interval(slopes[small]) if slopes[small] else None
        rhs = abs_interval(slopes[large]) if slopes[large] else None
        value = div(rhs, lhs) if lhs and rhs else None
        quotients[f"{small}_to_{large}"] = [enc(x) for x in value] if value else None
    OUT.write_text(json.dumps({
        "status": "conditional_finite_sample_slope_bounds_or_explicitly_unresolved",
        "confidence": "All twenty observable-mean intervals jointly cover with probability >=0.95 under iid exact CFTP draws and external Maurer-Pontil empirical Bernstein Theorem 4; slope and quotient propagation is deterministic exact rational arithmetic where defined.",
        "log_bound": "ln(800)<7 verified by finite rational Taylor sum",
        "cells": cells,
        "conditional_95_familywise_absolute_slope_quotient_intervals": quotients,
        "design_sha256": hashlib.sha256(design_path.read_bytes()).hexdigest(),
        "code_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "limitation": "The distribution-free support D<=3L^3 makes these intervals potentially wide; a null quotient is an unresolved result, not evidence against the scaling law. No exact-crossing or infinite-volume exponent claim."
    }, indent=2) + "\n")
    print("slope quotients resolved", {k: v is not None for k, v in quotients.items()}, flush=True)


if __name__ == "__main__":
    main()
