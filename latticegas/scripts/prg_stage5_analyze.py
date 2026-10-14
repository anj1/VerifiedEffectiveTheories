"""One-shot Binder-refined 8-to-12 quotient analysis with frozen comparison."""
import hashlib
import json
from fractions import Fraction as F
from pathlib import Path

import numpy as np

from prg_covcert import ROOT, RAW, enc
from prg_stage4_quotient_analyze import (
    BOOT, bootstrap_cell, fourier_eb, interval, load_cell,
    pair_result, rational_stats)

RESULT = ROOT / "grandcanonical_results"
OUT = RESULT / "prg_stage5_analysis.json"


def stage5_cell(L, r, n, bootstrap_seed):
    a, b = r.numerator, r.denominator
    path = RAW / f"cftp_stage5_quot_L{L}_r{a}_{b}_n{n}.jsonl"
    rows = [json.loads(line) for line in path.read_text().splitlines()]
    assert len(rows) == n and len({z["seed"] for z in rows}) == n
    assert all(z["success"] and z["algorithm"] == "cftp" and
               z["model_version"] == "grandcanonical-v4-prg" and
               z["L"] == L and z["r_num"] == a and z["r_den"] == b
               and z["replica"] == i for i, z in enumerate(rows))
    stats = rational_stats(rows, L)
    spec, S = fourier_eb(rows, L)
    boot = bootstrap_cell(rows, L, S, bootstrap_seed)
    item = {"L": L, "r": [a, b], "n": n,
            "raw_file": str(path.relative_to(ROOT)),
            "raw_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "max_horizon": max(z["horizon_updates"] for z in rows),
            "exact_rational_point": stats, "Fourier": spec,
            "bootstrap_95_exploratory": {
                "U4": interval(boot["U4"]),
                "slope": interval(boot["slope"]),
                "S": interval(boot["S"])}}
    return item, boot


def main():
    design_path = RESULT / "prg_stage5_design.json"
    selection_path = RESULT / "prg_stage5_selection.json"
    runs_path = RESULT / "prg_stage5_runs.json"
    selection = json.loads(selection_path.read_text())
    runs = json.loads(runs_path.read_text())
    assert runs["status"] == "both_fresh_fixed_count_exact_quotient_cells_completed"
    assert runs["selection_sha256"] == hashlib.sha256(selection_path.read_bytes()).hexdigest()
    r4, r8 = F(16, 25), F(*selection["selected_r"])
    items, boots = {}, {}
    for L, seed in ((4, 514004), (6, 514006)):
        items[L], boots[L] = load_cell(L, r4, 30000, seed)
        print("loaded original small quotient", L, flush=True)
    for L, seed in ((8, 515008), (12, 515012)):
        items[L], boots[L] = stage5_cell(L, r8, 12000, seed)
        print("loaded fresh refined quotient", L, flush=True)
    p4, b4 = pair_result(items, boots, 4, 6, r4, (F(12, 19), F(11, 17)))
    p8, b8 = pair_result(items, boots, 8, 12, r8, (F(7, 11), F(20, 31)))
    dt = interval(b8[0] - b4[0])
    ds = interval(b8[1] - b4[1])
    mismatch = interval(boots[8]["U4"] - boots[12]["U4"])
    q4 = [F(x) for x in p4["Q_S_conditional_95_familywise_interval"]]
    q8 = [F(x) for x in p8["Q_S_conditional_95_familywise_interval"]]
    result = {
        "status": "one_shot_refined_effective_dimension_comparison",
        "ensemble": "grandcanonical-v4-prg zero-field cubic Ising",
        "fresh_pair8_r": [r8.numerator, r8.denominator],
        "selection_uses_only_Binder": True,
        "cells": {str(L): items[L] for L in (4, 6, 8, 12)},
        "pairs": {"4_to_6": p4, "8_to_12": p8},
        "refined_8_minus_12_Binder_difference_bootstrap_95_exploratory": mismatch,
        "between_pair_difference_bootstrap_95_exploratory": {
            "y_t_large_minus_small": dt, "y_S_large_minus_small": ds},
        "predeclared_bootstrap_compatibility": {
            "thermal": dt[0] <= 0 <= dt[1],
            "correlation_scattering": ds[0] <= 0 <= ds[1]},
        "conditional_S_quotient_intervals_overlap": not (q4[1] < q8[0] or q8[1] < q4[0]),
        "confidence_boundary": "Four bounded-S empirical-Bernstein intervals have simultaneous coverage >=0.95 conditional on ideal iid CFTP and the external theorem; each crossing bracket separately has conditional >=0.95 coverage. Bootstrap thermal/scattering dimension intervals and compatibility have no finite-sample coverage theorem.",
        "numerical_boundary": "Moment and covariance point estimators are exact rational; Fourier means and variance are exact quadratic-algebraic enclosures; logarithms and bootstrap are exploratory floating point.",
        "bootstrap_resamples": BOOT,
        "bootstrap_fixed_seeds": {"4": 514004, "6": 514006, "8": 515008, "12": 515012},
        "design_sha256": hashlib.sha256(design_path.read_bytes()).hexdigest(),
        "selection_sha256": hashlib.sha256(selection_path.read_bytes()).hexdigest(),
        "runs_sha256": hashlib.sha256(runs_path.read_bytes()).hexdigest(),
        "code_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "stage4_analysis_sha256": selection["stage4_analysis_sha256"]
    }
    OUT.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({
        "r": result["fresh_pair8_r"],
        "Binder_delta": float(F(p8["point_U4_difference_small_minus_large"])),
        "Binder_delta_bootstrap": mismatch,
        "y_t": [p4["thermal_dimension_y_t_point"], p8["thermal_dimension_y_t_point"]],
        "y_S": [p4["scattering_dimension_y_S_point"], p8["scattering_dimension_y_S_point"]],
        "differences": result["between_pair_difference_bootstrap_95_exploratory"],
        "compatible": result["predeclared_bootstrap_compatibility"],
        "conditional_S_quotient_overlap": result["conditional_S_quotient_intervals_overlap"]
    }, indent=2), flush=True)


if __name__ == "__main__":
    main()
