"""Independent-sample phenomenological-RG quotients at frozen parameters.

Exact integer/rational sums determine the point slopes and algebraic Fourier
means. Bounded-S empirical-Bernstein intervals are finite-sample conditional
on iid exact draws and the external concentration theorem. Bootstrap slope
and dimension intervals are exploratory: no finite-sample coverage is claimed.
"""
import hashlib
import json
import math
from fractions import Fraction as F
from pathlib import Path

import numpy as np

from prg_analyze import Fourier_pair, sqrt_enclosure
from prg_covcert import ROOT, RAW, enc, sqrt_upper

OUT = ROOT / "grandcanonical_results" / "prg_stage4_quotient_analysis.json"
BOOT = 2000
CHUNK = 20


def alg_interval(A, B, d, denominator):
    assert denominator > 0
    sl, su = sqrt_enclosure(d)
    lo = F(A, denominator) + F(B, denominator) * (sl if B >= 0 else su)
    hi = F(A, denominator) + F(B, denominator) * (su if B >= 0 else sl)
    assert lo <= hi
    return lo, hi


def fourier_eb(rows, L):
    n, V = len(rows), L ** 3
    P = Q = P2 = Q2 = 0
    denom = d = None
    square_root_bounds = None
    float_values = np.empty(n)
    for i, row in enumerate(rows):
        p, q, dd, de = Fourier_pair(row)
        if denom is None:
            denom, d = de, dd
            square_root_bounds = sqrt_enclosure(d)
        assert de == denom and dd == d
        sl, su = square_root_bounds
        sample_lo = F(p) + q * (sl if q >= 0 else su)
        sample_hi = F(p) + q * (su if q >= 0 else sl)
        assert 0 <= sample_lo <= sample_hi <= V * denom
        P += p
        Q += q
        P2 += p * p + d * q * q
        Q2 += 2 * p * q
        float_values[i] = (p + q * math.sqrt(d)) / denom
    mean_lo, mean_hi = alg_interval(P, Q, d, n * denom)
    varA = n * P2 - P * P - d * Q * Q
    varB = n * Q2 - 2 * P * Q
    var_lo, var_hi = alg_interval(varA, varB, d, n * (n - 1) * denom ** 2)
    assert var_lo >= 0 and 0 <= mean_lo <= mean_hi <= V
    # Four S cells each use delta=1/80; ln(160)<6. The observed variance
    # itself is algebraic and enclosed outward by exact rational arithmetic.
    variance_normalized_upper = var_hi / V ** 2
    radius = sqrt_upper(F(12) * variance_normalized_upper / n) + F(14, n - 1)
    lo = max(F(0), mean_lo / V - radius) * V
    hi = min(F(1), mean_hi / V + radius) * V
    return {"point_mean_algebraic": {"P": P, "Q": Q, "radicand": d,
                                      "denominator": n * denom},
            "point_mean_interval": [enc(mean_lo), enc(mean_hi)],
            "sample_variance_interval": [enc(var_lo), enc(var_hi)],
            "conditional_95_familywise_S_interval": [enc(lo), enc(hi)],
            "normalized_radius_upper": enc(radius)}, float_values


def rational_stats(rows, L):
    n, V = len(rows), L ** 3
    X = [F(z["magnetization_sum_2"], V ** 2) for z in rows]
    Y = [F(z["magnetization_sum_4"], V ** 4) for z in rows]
    D = [z["disagreement_count"] for z in rows]
    a = sum(X, F(0)) / n
    b = sum(Y, F(0)) / n
    d = F(sum(D), n)
    ad = sum((X[i] * D[i] for i in range(n)), F(0)) / n - a * d
    bd = sum((Y[i] * D[i] for i in range(n)), F(0)) / n - b * d
    slope = -bd / (3 * a ** 2) + 2 * b * ad / (3 * a ** 3)
    return {"m2": enc(a), "m4": enc(b), "D": enc(d),
            "cov_m2_D": enc(ad), "cov_m4_D": enc(bd),
            "U4": enc(1 - b / (3 * a ** 2)),
            "binder_log_r_slope": enc(slope)}


def bootstrap_cell(rows, L, S, seed):
    n, V = len(rows), L ** 3
    x = np.fromiter((z["magnetization_sum_2"] / V ** 2 for z in rows),
                    dtype=np.float64, count=n)
    x4 = x * x
    D = np.fromiter((z["disagreement_count"] for z in rows),
                    dtype=np.float64, count=n)
    rng = np.random.default_rng(seed)
    U = np.empty(BOOT)
    slope = np.empty(BOOT)
    Sm = np.empty(BOOT)
    for start in range(0, BOOT, CHUNK):
        stop = min(start + CHUNK, BOOT)
        idx = rng.integers(0, n, size=(stop - start, n))
        a = x[idx].mean(axis=1)
        b = x4[idx].mean(axis=1)
        d = D[idx].mean(axis=1)
        ad = (x[idx] * D[idx]).mean(axis=1) - a * d
        bd = (x4[idx] * D[idx]).mean(axis=1) - b * d
        U[start:stop] = 1 - b / (3 * a * a)
        slope[start:stop] = -bd / (3 * a * a) + 2 * b * ad / (3 * a ** 3)
        Sm[start:stop] = S[idx].mean(axis=1)
    return {"U4": U, "slope": slope, "S": Sm}


def interval(values):
    return [float(np.quantile(values, .025)), float(np.quantile(values, .975))]


def load_cell(L, r, n, master_seed):
    a, b = r.numerator, r.denominator
    path = RAW / f"cftp_stage4_quot_L{L}_r{a}_{b}_n{n}.jsonl"
    rows = [json.loads(line) for line in path.read_text().splitlines()]
    assert len(rows) == n and len({z["seed"] for z in rows}) == n
    assert all(z["success"] and z["algorithm"] == "cftp" and
               z["model_version"] == "grandcanonical-v4-prg" and
               z["L"] == L and z["r_num"] == a and z["r_den"] == b
               for z in rows)
    stats = rational_stats(rows, L)
    spec, S = fourier_eb(rows, L)
    boot = bootstrap_cell(rows, L, S, master_seed)
    item = {"L": L, "r": [a, b], "n": n,
            "raw_file": str(path.relative_to(ROOT)),
            "raw_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "max_horizon": max(z["horizon_updates"] for z in rows),
            "exact_rational_point": stats, "Fourier": spec,
            "bootstrap_95_exploratory": {"U4": interval(boot["U4"]),
                                          "slope": interval(boot["slope"]),
                                          "S": interval(boot["S"])}}
    return item, boot


def pair_result(items, boots, small, large, r, bracket):
    a, b = items[small], items[large]
    pa = a["exact_rational_point"]
    pb = b["exact_rational_point"]
    du = F(pa["U4"]) - F(pb["U4"])
    qU = abs(F(pb["binder_log_r_slope"])) / abs(F(pa["binder_log_r_slope"]))
    Sla, Sua = [F(x) for x in a["Fourier"]["conditional_95_familywise_S_interval"]]
    Slb, Sub = [F(x) for x in b["Fourier"]["conditional_95_familywise_S_interval"]]
    assert Sla > 0 and Slb > 0
    qS_lo, qS_hi = Slb / Sua, Sub / Sla
    meanLa, meanUa = [F(x) for x in a["Fourier"]["point_mean_interval"]]
    meanLb, meanUb = [F(x) for x in b["Fourier"]["point_mean_interval"]]
    Spointa = (meanLa + meanUa) / 2
    Spointb = (meanLb + meanUb) / 2
    qS = Spointb / Spointa
    scale = F(large, small)
    log_scale = math.log(float(scale))
    yT = math.log(float(qU)) / log_scale
    yS = math.log(float(qS)) / log_scale
    u1, u2 = boots[small], boots[large]
    qU_b = np.abs(u2["slope"]) / np.abs(u1["slope"])
    qS_b = u2["S"] / u1["S"]
    yT_b = np.log(qU_b) / log_scale
    yS_b = np.log(qS_b) / log_scale
    du_b = u1["U4"] - u2["U4"]
    assert np.all(np.isfinite(yT_b)) and np.all(np.isfinite(yS_b))
    return {"sizes": [small, large], "r": [r.numerator, r.denominator],
            "certified_crossing_bracket": [enc(bracket[0]), enc(bracket[1])],
            "max_r_distance_to_bracket_crossing": enc(max(r - bracket[0], bracket[1] - r)),
            "point_U4_difference_small_minus_large": enc(du),
            "U4_difference_bootstrap_95_exploratory": interval(du_b),
            "Q_U_point_exact_rational": enc(qU),
            "Q_S_point_algebraic_interval": [enc(meanLb / meanUa),
                                              enc(meanUb / meanLa)],
            "Q_S_conditional_95_familywise_interval": [enc(qS_lo), enc(qS_hi)],
            "y_S_from_conditional_Q_S_interval_float_display": [
                math.log(float(qS_lo)) / log_scale,
                math.log(float(qS_hi)) / log_scale],
            "thermal_dimension_y_t_point": yT,
            "scattering_dimension_y_S_point": yS,
            "nu_eff_point": 1 / yT if yT > 0 else None,
            "eta_eff_point": 2 - yS,
            "bootstrap_95_exploratory": {"y_t": interval(yT_b),
                                          "y_S": interval(yS_b)},
            "warning": "The bootstrap dimension intervals have no finite-sample coverage theorem. The S quotient interval does, conditional on ideal iid streams, the Fourier bound, and external empirical Bernstein. Decimal digits of logarithmic y_S display are not interval-certified; the exact-rational Q_S interval is authoritative."}, (yT_b, yS_b)


def main():
    design_path = ROOT / "grandcanonical_results/prg_stage4_quotient_design.json"
    fallback_path = ROOT / "grandcanonical_results/prg_stage4_fallback_design.json"
    decision_path = ROOT / "grandcanonical_results/prg_stage4_postresult_rule.json"
    selection_path = ROOT / "grandcanonical_results/prg_stage4_quotient_selection.json"
    design = json.loads(design_path.read_text())
    selection = json.loads(selection_path.read_text())
    r4 = F(*design["pair_4_to_6"]["sampling_r"])
    r8 = F(*selection["selected_r"])
    assert r4 == F(16, 25)
    params = {4: (r4, 30000, 514004), 6: (r4, 30000, 514006),
              8: (r8, 15000, 514008), 12: (r8, 15000, 514012)}
    items, boots = {}, {}
    for L, (r, n, seed) in params.items():
        items[L], boots[L] = load_cell(L, r, n, seed)
        print("loaded quotient cell", L, r, n, flush=True)
    p4, b4 = pair_result(items, boots, 4, 6, r4, (F(12, 19), F(11, 17)))
    p8, b8 = pair_result(items, boots, 8, 12, r8,
                         tuple(F(x) for x in selection["certified_crossing_bracket"]))
    dt = b8[0] - b4[0]
    ds = b8[1] - b4[1]
    it, iS = interval(dt), interval(ds)
    result = {"status": "finite_volume_effective_dimensions_at_frozen_crossing_approximations",
              "microscopic_ensemble": "grandcanonical-v4-prg zero-field Ising",
              "exact_identity": "dU4/dlog(r) from covariance with disagreement count D; proved in GrandCanonicalPRG.lean",
              "confidence_boundary": "Four S intervals have joint coverage >=0.95 under ideal iid CFTP streams, external empirical-Bernstein theorem, and the exact S<=V bound. Thermal-dimension/bootstrap intervals are exploratory, not finite-sample certified.",
              "numerical_boundary": "m2,m4,D,covariances and slope points exact rational; Fourier mean and variance enclosed as integer-coefficient quadratic algebraic numbers; logarithms and bootstrap use ordinary floating point for exploratory dimensions.",
              "bootstrap_resamples": BOOT,
              "bootstrap_fixed_seeds": {str(L): params[L][2] for L in params},
              "cells": {str(L): items[L] for L in items},
              "pairs": {"4_to_6": p4, "8_to_12": p8},
              "between_pair_difference_bootstrap_95_exploratory": {"y_t_large_minus_small": it,
                                                                    "y_S_large_minus_small": iS},
              "predeclared_bootstrap_compatibility": {"thermal": it[0] <= 0 <= it[1],
                                                       "correlation_scattering": iS[0] <= 0 <= iS[1]},
              "conditional_S_quotient_intervals_overlap": not (
                  F(p4["Q_S_conditional_95_familywise_interval"][1]) <
                  F(p8["Q_S_conditional_95_familywise_interval"][0]) or
                  F(p8["Q_S_conditional_95_familywise_interval"][1]) <
                  F(p4["Q_S_conditional_95_familywise_interval"][0])),
              "design_sha256": hashlib.sha256(design_path.read_bytes()).hexdigest(),
              "fallback_design_sha256": hashlib.sha256(fallback_path.read_bytes()).hexdigest(),
              "postresult_rule_sha256": hashlib.sha256(decision_path.read_bytes()).hexdigest(),
              "selection_sha256": hashlib.sha256(selection_path.read_bytes()).hexdigest(),
              "code_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    OUT.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"pair4": p4["bootstrap_95_exploratory"],
                      "pair8": p8["bootstrap_95_exploratory"],
                      "difference": result["between_pair_difference_bootstrap_95_exploratory"],
                      "compatible": result["predeclared_bootstrap_compatibility"]}, indent=2))


if __name__ == "__main__":
    main()
