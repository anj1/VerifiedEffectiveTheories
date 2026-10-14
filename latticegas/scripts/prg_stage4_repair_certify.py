"""Final narrowed-crossing sign test after the first 4-to-6 endpoint failed.

Each crossing has a separate conditional 95% familywise confidence procedure.
Exact Fraction arithmetic is used for all numerical sign decisions. The iid
stream law and empirical-Bernstein theorem remain external premises.
"""
import hashlib
import json
import math
from fractions import Fraction as F
from pathlib import Path

from prg_covcert import ROOT, RAW, eb_interval, enc, moment2

OUT = ROOT / "grandcanonical_results" / "prg_stage4_repair_certificate.json"
SPECS = [
    ("4_to_6", "low", 4, F(12, 19), 20000, F(67, 50),
     "cftp_stage4_confirm_L4_r12_19_n10000.jsonl",
     "cftp_stage4_repair_low_L4_r12_19_n20000.jsonl"),
    ("4_to_6", "low", 6, F(12, 19), 20000, F(67, 50),
     "cftp_stage4_confirm_L6_r12_19_n10000.jsonl",
     "cftp_stage4_repair_low_L6_r12_19_n20000.jsonl"),
    ("4_to_6", "high", 4, F(11, 17), 30000, F(41, 25),
     "cftp_stage4_repair_pilot_L4_r11_17_n2000.jsonl",
     "cftp_stage4_repair_high_L4_r11_17_n30000.jsonl"),
    ("4_to_6", "high", 6, F(11, 17), 30000, F(41, 25),
     "cftp_stage4_repair_pilot_L6_r11_17_n2000.jsonl",
     "cftp_stage4_repair_high_L6_r11_17_n30000.jsonl"),
    ("8_to_12", "high", 8, F(9, 14), 40000, F(81, 50),
     "cftp_stage4_pilot_L8_r9_14_n1000.jsonl",
     "cftp_stage4_confirm_L8_r9_14_n40000.jsonl"),
    ("8_to_12", "high", 12, F(9, 14), 40000, F(81, 50),
     "cftp_stage4_pilot_L12_r9_14_n1000.jsonl",
     "cftp_stage4_confirm_L12_r9_14_n40000_recovered.jsonl"),
]


def cell(spec):
    pair, side, L, r, n, c, pilot_file, confirm_file = spec
    pp, hp = RAW / pilot_file, RAW / confirm_file
    pilot = [json.loads(line) for line in pp.read_text().splitlines()]
    rows = [json.loads(line) for line in hp.read_text().splitlines()]
    assert len(rows) == n and len({z["seed"] for z in rows}) == n
    assert len({z["seed"] for z in pilot}) == len(pilot)
    assert not {z["seed"] for z in pilot}.intersection(z["seed"] for z in rows)
    assert all(z["success"] and z["algorithm"] == "cftp" and
               z["model_version"] == "grandcanonical-v4-prg" and
               z["L"] == L and z["r_num"] == r.numerator and
               z["r_den"] == r.denominator for z in rows)
    pa = sum(moment2(pilot, L), F(0)) / len(pilot)
    a0 = F(round(pa * 1000000), 1000000)
    assert 0 <= c * a0 <= 1
    x = moment2(rows, L)
    y = [v * v - 2 * c * a0 * v for v in x]
    yl, yu, ym, yv, yr = eb_interval(y, -(c * a0) ** 2,
                                      max(F(0), 1 - 2 * c * a0))
    al, au, am, av, ar = eb_interval(x, F(0), F(1))
    g_lo, g_hi = yl + c * a0 ** 2, yu + c * a0 ** 2
    e = max(abs(al - a0), abs(au - a0))
    f_lo, f_hi = g_lo - c * e ** 2, g_hi
    b = sum((v * v for v in x), F(0)) / n
    sign = "positive" if f_lo > 0 else "negative" if f_hi < 0 else "unresolved"
    return {"pair": pair, "side": side, "L": L,
            "r": [r.numerator, r.denominator], "n": n,
            "threshold_c": enc(c), "pilot_a0": enc(a0),
            "pilot_file": str(pp.relative_to(ROOT)),
            "pilot_sha256": hashlib.sha256(pp.read_bytes()).hexdigest(),
            "confirm_file": str(hp.relative_to(ROOT)),
            "confirm_sha256": hashlib.sha256(hp.read_bytes()).hexdigest(),
            "max_horizon": max(z["horizon_updates"] for z in rows),
            "m2_point": enc(am), "m4_point": enc(b),
            "U4_point": enc(1 - b / (3 * am ** 2)),
            "F_point": enc(b - c * am ** 2),
            "a_interval": [enc(al), enc(au)],
            "G_interval": [enc(g_lo), enc(g_hi)],
            "F_interval": [enc(f_lo), enc(f_hi)],
            "F_sign": sign, "a_radius": enc(ar), "Y_radius": enc(yr),
            "a_variance": enc(av), "Y_variance": enc(yv)}


def main():
    assert sum((F(6) ** k / math.factorial(k) for k in range(12)), F(0)) > 320
    points = [cell(spec) for spec in SPECS]
    lookup = {(v["pair"], v["side"], v["L"]): v for v in points}
    old_path = ROOT / "grandcanonical_results/prg_covcert.json"
    old = json.loads(old_path.read_text())
    low8 = {v["L"]: v for v in old["cells"] if v["r"] == [7, 11]}
    for v in low8.values():
        assert hashlib.sha256((ROOT / v["holdout_raw"]).read_bytes()).hexdigest() == v["holdout_sha256"]
    c46 = (lookup[("4_to_6", "low", 4)]["F_sign"] == "positive" and
           lookup[("4_to_6", "low", 6)]["F_sign"] == "negative" and
           lookup[("4_to_6", "high", 4)]["F_sign"] == "negative" and
           lookup[("4_to_6", "high", 6)]["F_sign"] == "positive")
    c812 = (low8[8]["F_sign"] == "positive" and
            low8[12]["F_sign"] == "negative" and
            lookup[("8_to_12", "high", 8)]["F_sign"] == "negative" and
            lookup[("8_to_12", "high", 12)]["F_sign"] == "positive")
    result = {"status": "conditional_finite_sample_sign_test",
              "method": "pilot-frozen centered Binder F with exact-rational empirical Bernstein",
              "confidence": "Each pair separately has familywise coverage >=0.95 under ideal iid CFTP streams and external Maurer-Pontil Theorem 4; joint coverage >=0.90 by union bound.",
              "alpha_accounting": "Eight two-sided intervals per pair, each delta=1/160; for 8-to-12, four low-side intervals come from the earlier prg_covcert.json and four high-side intervals are new.",
              "old_8_to_12_low_certificate_sha256": hashlib.sha256(old_path.read_bytes()).hexdigest(),
              "old_8_to_12_low_signs": {str(L): low8[L]["F_sign"] for L in (8, 12)},
              "new_cells": points,
              "crossing_4_to_6_certified": c46,
              "crossing_4_to_6_bracket": [[12, 19], [11, 17]] if c46 else None,
              "crossing_8_to_12_certified": c812,
              "crossing_8_to_12_bracket": [[7, 11], [9, 14]] if c812 else None,
              "code_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    OUT.write_text(json.dumps(result, indent=2) + "\n")
    for v in points:
        print(v["pair"], v["side"], v["L"], v["F_sign"],
              f'F={float(F(v["F_point"])):+.7g}',
              f'box={[float(F(q)) for q in v["F_interval"]]}', flush=True)
    print("crossings", c46, c812)


if __name__ == "__main__":
    main()
