"""Fresh high-side confirmatory batch after the 5,000-draw design pilot.

The low-side signs are taken only from prg_covcert.json. Four low-side and
four new high-side two-sided concentration events each have delta=1/160;
their union failure probability is at most 0.05 under ideal iid streams.
"""
import hashlib
import json
from fractions import Fraction as F
from pathlib import Path

from prg_covcert import ROOT, RAW, eb_interval, enc, moment2
from prg_analyze import fourier_interval

OUT = ROOT / "grandcanonical_results" / "prg_covcert2.json"
N = 30000
C = F(7, 4)


def cell(L):
    pilot_path = RAW / f"cftp_covhold_L{L}_r20_31_n5000.jsonl"
    holdout_path = RAW / f"cftp_covstage2_L{L}_r20_31_n{N}.jsonl"
    pilot = [json.loads(line) for line in pilot_path.read_text().splitlines()]
    rows = [json.loads(line) for line in holdout_path.read_text().splitlines()]
    assert len(pilot) == 5000 and len(rows) == N
    assert len({z["seed"] for z in rows}) == N
    assert not ({z["seed"] for z in rows} & {z["seed"] for z in pilot})
    assert all(z["success"] and z["algorithm"] == "cftp" and z["L"] == L
               and z["r_num"] == 20 and z["r_den"] == 31 for z in rows)
    pilot_a = sum(moment2(pilot, L), F(0)) / 5000
    a0 = F(round(pilot_a * 1000000), 1000000)
    assert 0 <= C * a0 <= 1
    x = moment2(rows, L)
    y = [t * t - 2 * C * a0 * t for t in x]
    ylo, yhi = -(C * a0) ** 2, max(F(0), 1 - 2 * C * a0)
    yl, yu, ym, yv, yr = eb_interval(y, ylo, yhi)
    al, au, am, av, ar = eb_interval(x, F(0), F(1))
    g_lo, g_hi = yl + C * a0 ** 2, yu + C * a0 ** 2
    e = max(abs(al - a0), abs(au - a0))
    f_lo, f_hi = g_lo - C * e ** 2, g_hi
    sign = "positive" if f_lo > 0 else "negative" if f_hi < 0 else "unresolved"
    b = sum((t * t for t in x), F(0)) / N
    D = sum((z["disagreement_count"] for z in rows), 0)
    Dmean = F(D, N)
    aD = sum((x[i] * rows[i]["disagreement_count"] for i in range(N)), F(0)) / N - am * Dmean
    bD = sum((x[i] * x[i] * rows[i]["disagreement_count"] for i in range(N)), F(0)) / N - b * Dmean
    binder_slope = -bD / (3 * am ** 2) + 2 * b * aD / (3 * am ** 3)
    return {"L": L, "r": [20, 31], "n": N, "threshold_c": enc(C),
            "pilot_a0": enc(a0), "pilot_raw": str(pilot_path.relative_to(ROOT)),
            "holdout_raw": str(holdout_path.relative_to(ROOT)),
            "pilot_sha256": hashlib.sha256(pilot_path.read_bytes()).hexdigest(),
            "holdout_sha256": hashlib.sha256(holdout_path.read_bytes()).hexdigest(),
            "m2_mean": enc(am), "m4_mean": enc(b),
            "D_mean": enc(Dmean), "binder_log_r_slope_point_exploratory": enc(binder_slope),
            "S_spin_kmin_algebraic_point_exploratory": fourier_interval(rows),
            "a_interval": [enc(al), enc(au)],
            "G_interval": [enc(g_lo), enc(g_hi)],
            "F_interval": [enc(f_lo), enc(f_hi)],
            "F_point": enc(b - C * am ** 2), "F_sign": sign,
            "a_radius": enc(ar), "Y_radius": enc(yr),
            "a_variance": enc(av), "Y_variance": enc(yv)}


def main():
    low_path = ROOT / "grandcanonical_results" / "prg_covcert.json"
    low = json.loads(low_path.read_text())
    lowcells = {z["L"]: z for z in low["cells"] if z["r"] == [7, 11]}
    for z in lowcells.values():
        assert hashlib.sha256((ROOT / z["holdout_raw"]).read_bytes()).hexdigest() == z["holdout_sha256"]
        assert hashlib.sha256((ROOT / z["pilot_raw"]).read_bytes()).hexdigest() == z["pilot_sha256"]
    cells = [cell(L) for L in (8, 12)]
    crossing = (lowcells[8]["F_sign"] == "positive" and
                lowcells[12]["F_sign"] == "negative" and
                cells[0]["F_sign"] == "negative" and
                cells[1]["F_sign"] == "positive")
    result = {"method": "pilot_frozen_centered_Binder_sign_stage2",
              "confidence_conditional_on_ideal_iid": "at_least_0.95",
              "alpha_accounting": "Four low-side intervals from stage 1 and four new high-side intervals at delta=1/160 each; sum of eight failure bounds is 0.05. Old high-side confirmatory data are design-only for this stage.",
              "stage1_low_certificate": "grandcanonical_results/prg_covcert.json",
              "stage1_low_certificate_sha256": hashlib.sha256(low_path.read_bytes()).hexdigest(),
              "stage1_low_signs": {str(L): lowcells[L]["F_sign"] for L in (8, 12)},
              "cells": cells,
              "certified_8_to_12_crossing": crossing,
              "crossing_bracket": [[7, 11], [20, 31]] if crossing else None,
              "code_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    OUT.write_text(json.dumps(result, indent=2) + "\n")
    for z in cells:
        print(f'L={z["L"]}: {z["F_sign"]}; '
              f'F_point={float(F(z["F_point"])):.7g}, '
              f'F_box=({float(F(z["F_interval"][0])):.7g}, '
              f'{float(F(z["F_interval"][1])):.7g})')
    print("certified_crossing:", crossing)


if __name__ == "__main__":
    main()
