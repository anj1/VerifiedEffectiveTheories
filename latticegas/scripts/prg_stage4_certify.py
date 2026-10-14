"""Exact-rational, pilot-frozen Binder-sign certificates for two size pairs.

Ideal iid CFTP streams and Maurer--Pontil (2009), Theorem 4, are external
probabilistic premises. Lean proves the deterministic sign-to-crossing logic.
All numerical sign arithmetic here is Fraction/integer arithmetic.
"""
import hashlib
import json
import math
from fractions import Fraction as F
from pathlib import Path

from prg_covcert import ROOT, RAW, eb_interval, enc, moment2

DESIGN = ROOT / "grandcanonical_results" / "prg_stage4_design.json"
OUT = ROOT / "grandcanonical_results" / "prg_stage4_certificate.json"


def pilot_path(L, num, den):
    if (num, den) == (16, 25) and L in (4, 6):
        return RAW / f"cftp_prg_L{L}_r16_25_n2000.jsonl"
    return RAW / f"cftp_stage4_pilot_L{L}_r{num}_{den}_n1000.jsonl"


def cell(spec):
    L, (num, den), n = spec["L"], spec["r"], spec["n"]
    c = F(*spec["c"])
    pp = pilot_path(L, num, den)
    hp = RAW / f"cftp_stage4_confirm_L{L}_r{num}_{den}_n{n}.jsonl"
    pilot = [json.loads(line) for line in pp.read_text().splitlines()]
    rows = [json.loads(line) for line in hp.read_text().splitlines()]
    assert len(rows) == n and len(pilot) in (1000, 2000)
    pseed, hseed = {z["seed"] for z in pilot}, {z["seed"] for z in rows}
    assert len(pseed) == len(pilot) and len(hseed) == n and not pseed.intersection(hseed)
    assert all(z["success"] and z["algorithm"] == "cftp" and
               z["model_version"] == "grandcanonical-v4-prg" and
               z["L"] == L and z["r_num"] == num and z["r_den"] == den
               for z in rows)
    pa = sum(moment2(pilot, L), F(0)) / len(pilot)
    a0 = F(round(pa * 1000000), 1000000)
    assert 0 <= c * a0 <= 1
    x = moment2(rows, L)
    y = [t * t - 2 * c * a0 * t for t in x]
    yl, yu, ym, yv, yr = eb_interval(
        y, -(c * a0) ** 2, max(F(0), 1 - 2 * c * a0))
    al, au, am, av, ar = eb_interval(x, F(0), F(1))
    g_lo, g_hi = yl + c * a0 ** 2, yu + c * a0 ** 2
    e = max(abs(al - a0), abs(au - a0))
    f_lo, f_hi = g_lo - c * e ** 2, g_hi
    sign = "positive" if f_lo > 0 else "negative" if f_hi < 0 else "unresolved"
    b = sum((t * t for t in x), F(0)) / n
    return {"pair": spec["pair"], "side": spec["side"], "L": L,
            "r": [num, den], "n": n, "threshold_c": enc(c),
            "pilot_a0": enc(a0), "pilot_raw": str(pp.relative_to(ROOT)),
            "pilot_sha256": hashlib.sha256(pp.read_bytes()).hexdigest(),
            "confirm_raw": str(hp.relative_to(ROOT)),
            "confirm_sha256": hashlib.sha256(hp.read_bytes()).hexdigest(),
            "max_horizon": max(z["horizon_updates"] for z in rows),
            "mean_m2": enc(am), "mean_m4": enc(b),
            "U4_point": enc(1 - b / (3 * am ** 2)),
            "a_interval": [enc(al), enc(au)],
            "G_interval": [enc(g_lo), enc(g_hi)],
            "F_interval": [enc(f_lo), enc(f_hi)],
            "F_point": enc(b - c * am ** 2), "F_sign": sign,
            "a_radius": enc(ar), "Y_radius": enc(yr),
            "a_variance": enc(av), "Y_variance": enc(yv)}


def main():
    assert sum((F(6) ** k / math.factorial(k) for k in range(12)), F(0)) > 320
    design = json.loads(DESIGN.read_text())
    points = [cell(spec) for spec in design["new_cells"]]
    lookup = {(z["pair"], z["side"], z["L"]): z for z in points}
    old = json.loads((ROOT / "grandcanonical_results/prg_covcert.json").read_text())
    oldlow = {z["L"]: z for z in old["cells"] if z["r"] == [7, 11]}
    for z in oldlow.values():
        assert hashlib.sha256((ROOT / z["holdout_raw"]).read_bytes()).hexdigest() == z["holdout_sha256"]
    c46 = (lookup[("4_to_6", "low", 4)]["F_sign"] == "positive" and
           lookup[("4_to_6", "low", 6)]["F_sign"] == "negative" and
           lookup[("4_to_6", "high", 4)]["F_sign"] == "negative" and
           lookup[("4_to_6", "high", 6)]["F_sign"] == "positive")
    c812 = (oldlow[8]["F_sign"] == "positive" and
            oldlow[12]["F_sign"] == "negative" and
            lookup[("8_to_12", "high", 8)]["F_sign"] == "negative" and
            lookup[("8_to_12", "high", 12)]["F_sign"] == "positive")
    result = {"method": "pilot_frozen_centered_Binder_signs",
              "statistical_boundary": "Each pair has familywise confidence at least 0.95, conditional on ideal iid CFTP draws and external Maurer-Pontil Theorem 4. Joint coverage of the two crossing claims is at least 0.90 by union bound.",
              "eight_events_per_pair": "each two-sided interval uses delta=1/160 and rational ln(320)<6",
              "design_sha256": hashlib.sha256(DESIGN.read_bytes()).hexdigest(),
              "old_low_certificate_sha256": hashlib.sha256((ROOT / "grandcanonical_results/prg_covcert.json").read_bytes()).hexdigest(),
              "new_cells": points,
              "old_8_to_12_low_signs": {str(L): oldlow[L]["F_sign"] for L in (8, 12)},
              "crossing_4_to_6_certified": c46,
              "crossing_4_to_6_bracket": [[12, 19], [16, 25]] if c46 else None,
              "crossing_8_to_12_certified": c812,
              "crossing_8_to_12_bracket": [[7, 11], [9, 14]] if c812 else None,
              "code_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    OUT.write_text(json.dumps(result, indent=2) + "\n")
    for z in points:
        lo, hi = (float(F(v)) for v in z["F_interval"])
        print(z["pair"], z["side"], f'L={z["L"]}', z["F_sign"],
              f'F_point={float(F(z["F_point"])):+.7g}',
              f'F_box=[{lo:+.7g},{hi:+.7g}]', flush=True)
    print("crossings", c46, c812)


if __name__ == "__main__":
    main()
