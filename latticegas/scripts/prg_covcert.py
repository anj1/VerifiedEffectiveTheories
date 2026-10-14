"""Pilot-frozen, exact-arithmetic covariance-aware Binder sign test.

The concentration theorem is Maurer--Pontil (2009), Theorem 4, conditional
on iid exact equilibrium draws. Its proof is external to Lean. Every bound
calculation below uses integers/Fraction; ln(320) < 6 is a rationally checked
finite-Taylor fact, so no floating point enters the sign decision.
"""
import hashlib
import json
import math
from fractions import Fraction as F
from pathlib import Path

ROOT = Path(__file__).resolve().parent
RAW = ROOT / "grandcanonical_data" / "prg_raw"
OUT = ROOT / "grandcanonical_results" / "prg_covcert.json"
CELLS = [(8, 7, 11, F(127, 100)), (12, 7, 11, F(127, 100)),
         (8, 20, 31, F(9, 5)), (12, 20, 31, F(9, 5))]
HOLDOUT_N = 5000
SQRT_DIGITS = 30
LOG_UPPER = F(6)


def enc(q):
    return str(q.numerator) + "/" + str(q.denominator)


def sqrt_upper(q):
    assert q >= 0
    scale = 10 ** SQRT_DIGITS
    floor = math.isqrt(q.numerator * scale * scale // q.denominator)
    return F(floor + 1, scale)


def eb_interval(values, lower, upper):
    """Conservative MP interval with delta=.05/8 and ln(320)<6."""
    n = len(values)
    assert n > 1 and all(lower <= x <= upper for x in values)
    span = upper - lower
    mean = sum(values, F(0)) / n
    variance = (sum((x - mean) ** 2 for x in values) / (n - 1))
    radius = sqrt_upper(2 * variance * LOG_UPPER / n) + \
        F(7) * LOG_UPPER * span / (3 * (n - 1))
    return max(lower, mean - radius), min(upper, mean + radius), mean, variance, radius


def load(L, num, den, pilot):
    if pilot:
        name = (f"cftp_explore_L{L}_r20_31_n1000.jsonl" if (num, den) == (20, 31)
                else f"cftp_prg_L{L}_r{num}_{den}_n1000.jsonl")
    else:
        name = f"cftp_covhold_L{L}_r{num}_{den}_n{HOLDOUT_N}.jsonl"
    path = RAW / name
    rows = [json.loads(line) for line in path.read_text().splitlines()]
    expected = 1000 if pilot else HOLDOUT_N
    assert len(rows) == expected
    assert len({r["seed"] for r in rows}) == expected
    assert all(r["success"] and r["algorithm"] == "cftp" and r["L"] == L
               and r["r_num"] == num and r["r_den"] == den for r in rows)
    return rows, path


def moment2(rows, L):
    V = L ** 3
    return [F(r["magnetization_sum_2"], V ** 2) for r in rows]


def cell(L, num, den, c):
    pilot, pp = load(L, num, den, True)
    holdout, hp = load(L, num, den, False)
    assert not ({z["seed"] for z in pilot} & {z["seed"] for z in holdout})
    pilot_a = sum(moment2(pilot, L), F(0)) / len(pilot)
    # Freeze a compact rational center before inspecting the holdout.
    a0 = F(round(pilot_a * 1000000), 1000000)
    assert 0 <= c * a0 <= 1
    x = moment2(holdout, L)
    y = [t * t - 2 * c * a0 * t for t in x]
    ylo = -(c * a0) ** 2
    yhi = max(F(0), 1 - 2 * c * a0)
    yl, yu, ym, yv, yr = eb_interval(y, ylo, yhi)
    al, au, am, av, ar = eb_interval(x, F(0), F(1))
    g_lo, g_hi = yl + c * a0 ** 2, yu + c * a0 ** 2
    e = max(abs(al - a0), abs(au - a0))
    f_lo, f_hi = g_lo - c * e ** 2, g_hi
    # The true ratio R=b/a² is above/below c exactly when F=b-ca² is.
    sign = "positive" if f_lo > 0 else "negative" if f_hi < 0 else "unresolved"
    return {"L": L, "r": [num, den], "threshold_c": enc(c),
            "pilot_center_a0": enc(a0), "pilot_raw": str(pp.relative_to(ROOT)),
            "holdout_raw": str(hp.relative_to(ROOT)), "n_holdout": len(x),
            "pilot_sha256": hashlib.sha256(pp.read_bytes()).hexdigest(),
            "holdout_sha256": hashlib.sha256(hp.read_bytes()).hexdigest(),
            "a_interval": [enc(al), enc(au)],
            "G_interval": [enc(g_lo), enc(g_hi)],
            "F_interval": [enc(f_lo), enc(f_hi)], "F_sign": sign,
            "a_mean": enc(am), "Y_mean": enc(ym),
            "a_radius": enc(ar), "Y_radius": enc(yr),
            "a_variance": enc(av), "Y_variance": enc(yv),
            "F_point": enc(sum(t * t for t in x) / len(x) - c * am ** 2)}


def main():
    # e^6 > 320 via a finite rational Taylor partial sum.
    assert sum((F(6) ** k / math.factorial(k) for k in range(12)), F(0)) > 320
    cells = [cell(*args) for args in CELLS]
    lookup = {(v["L"], tuple(v["r"])): v for v in cells}
    low = [lookup[(L, (7, 11))]["F_sign"] for L in (8, 12)]
    high = [lookup[(L, (20, 31))]["F_sign"] for L in (8, 12)]
    crossing = low == ["positive", "negative"] and high == ["negative", "positive"]
    result = {"method": "pilot_frozen_centered_Binder_sign",
              "confidence_conditional_on_ideal_iid": "at_least_0.95",
              "concentration": "Maurer-Pontil 2009 Theorem 4; 8 two-sided intervals each at delta=1/160",
              "log_bound": "ln(320)<6 by rational Taylor partial sum; all subsequent interval arithmetic exact rational",
              "Lean_logic": ["GrandCanonical.centered_binder_identity",
                             "GrandCanonical.centered_binder_ratio_lt",
                             "GrandCanonical.centered_binder_ratio_gt"],
              "cells": cells, "certified_8_to_12_crossing": crossing,
              "claim": "conditional finite-volume crossing in (7/11,20/31)" if crossing else
                       "no second crossing certified by these finite-sample bounds",
              "external_assumptions": ["ideal iid random streams", "external empirical-Bernstein theorem"],
              "code_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    OUT.write_text(json.dumps(result, indent=2) + "\n")
    for z in cells:
        print(f'L={z["L"]}, r={z["r"]}: {z["F_sign"]}; '
              f'F_point={float(F(z["F_point"])):.7g}, '
              f'F_box=({float(F(z["F_interval"][0])):.7g}, '
              f'{float(F(z["F_interval"][1])):.7g})')
    print("certified_crossing:", crossing)


if __name__ == "__main__":
    main()
