"""Reallocate *existing* confirmation data to one 5% familywise budget.

This is a post-hoc sensitivity calculation, not a fresh predeclared test.
The output records that qualification. All sign/quotient arithmetic is rational.
"""
import hashlib
import json
import math
from fractions import Fraction as F
from pathlib import Path

from prg_analyze import Fourier_pair, sqrt_enclosure
from prg_covcert import RAW, ROOT, enc, moment2, sqrt_upper
from prg_stage4_repair_certify import SPECS

OUT = ROOT / "grandcanonical_results/prg_final_global_cert.json"
DELTA = F(1, 400)
LOG_UPPER = F(7)  # ln(2/delta) = ln(800) < 7.


def eb(values, lower, upper):
    n = len(values)
    assert n > 1 and all(lower <= x <= upper for x in values)
    mean = sum(values, F(0)) / n
    var = (sum((x - mean) ** 2 for x in values) / (n - 1))
    radius = sqrt_upper(2 * var * LOG_UPPER / n) + \
        F(7) * LOG_UPPER * (upper - lower) / (3 * (n - 1))
    return max(lower, mean - radius), min(upper, mean + radius)


def crossing_cell(pair, side, L, r, c, pilot_name, sample_name):
    pp, hp = RAW / pilot_name, RAW / sample_name
    pilot = [json.loads(line) for line in pp.read_text().splitlines()]
    rows = [json.loads(line) for line in hp.read_text().splitlines()]
    assert not ({z["seed"] for z in pilot} & {z["seed"] for z in rows})
    assert len({z["seed"] for z in rows}) == len(rows)
    assert all(z["success"] and z["algorithm"] == "cftp" and
               z["L"] == L and z["r_num"] == r.numerator and
               z["r_den"] == r.denominator for z in rows)
    a0 = F(round(sum(moment2(pilot, L), F(0)) / len(pilot) * 1000000), 1000000)
    assert 0 <= c * a0 <= 1
    x = moment2(rows, L)
    y = [v * v - 2 * c * a0 * v for v in x]
    yl, yu = eb(y, -(c * a0) ** 2, max(F(0), 1 - 2 * c * a0))
    al, au = eb(x, F(0), F(1))
    e = max(abs(al - a0), abs(au - a0))
    flo, fhi = yl + c * a0 ** 2 - c * e ** 2, yu + c * a0 ** 2
    return {"pair": pair, "side": side, "L": L, "r": enc(r), "n": len(rows),
            "threshold_c": enc(c), "pilot_center": enc(a0),
            "pilot_file": str(pp.relative_to(ROOT)),
            "pilot_sha256": hashlib.sha256(pp.read_bytes()).hexdigest(),
            "sample_file": str(hp.relative_to(ROOT)),
            "sample_sha256": hashlib.sha256(hp.read_bytes()).hexdigest(),
            "F_interval": [enc(flo), enc(fhi)],
            "sign": "positive" if flo > 0 else "negative" if fhi < 0 else "unresolved"}


def algebraic_bounds(a, b, d, denom):
    sl, su = sqrt_enclosure(d)
    return (F(a, denom) + F(b, denom) * (sl if b >= 0 else su),
            F(a, denom) + F(b, denom) * (su if b >= 0 else sl))


def fourier_cell(L, r, sample_name):
    hp = RAW / sample_name
    rows = [json.loads(line) for line in hp.read_text().splitlines()]
    n, V = len(rows), L ** 3
    assert len({z["seed"] for z in rows}) == n
    assert all(z["success"] and z["algorithm"] == "cftp" and
               z["L"] == L and z["r_num"] == r.numerator and
               z["r_den"] == r.denominator for z in rows)
    ptotal = qtotal = p2total = q2total = 0
    d = denominator = None
    for row in rows:
        p, q, dd, de = Fourier_pair(row)
        if d is None:
            d, denominator = dd, de
        assert dd == d and de == denominator
        ptotal += p
        qtotal += q
        p2total += p * p + d * q * q
        q2total += 2 * p * q
    mean_lo, mean_hi = algebraic_bounds(ptotal, qtotal, d, n * denominator)
    var_hi = algebraic_bounds(n * p2total - ptotal ** 2 - d * qtotal ** 2,
                              n * q2total - 2 * ptotal * qtotal,
                              d, n * (n - 1) * denominator ** 2)[1]
    assert 0 <= mean_lo <= mean_hi <= V and var_hi >= 0
    radius = sqrt_upper(F(14) * var_hi / (V * V * n)) + F(49, 3 * (n - 1))
    lo = max(F(0), mean_lo / V - radius) * V
    hi = min(F(1), mean_hi / V + radius) * V
    return {"L": L, "r": enc(r), "n": n,
            "sample_file": str(hp.relative_to(ROOT)),
            "sample_sha256": hashlib.sha256(hp.read_bytes()).hexdigest(),
            "S_interval": [enc(lo), enc(hi)]}


def main():
    assert sum((F(7) ** k / math.factorial(k) for k in range(12)), F(0)) > 800
    cells = [crossing_cell(pair, side, L, r, c, pilot, confirm)
             for pair, side, L, r, _n, c, pilot, confirm in SPECS[:4]]
    for L in (8, 12):
        cells.append(crossing_cell("8_to_12", "low", L, F(7, 11), F(127, 100),
                     f"cftp_prg_L{L}_r7_11_n1000.jsonl",
                     f"cftp_covhold_L{L}_r7_11_n5000.jsonl"))
        cells.append(crossing_cell("8_to_12", "high", L, F(20, 31), F(7, 4),
                     f"cftp_covhold_L{L}_r20_31_n5000.jsonl",
                     f"cftp_covstage2_L{L}_r20_31_n30000.jsonl"))
    signs = {(v["pair"], v["side"], v["L"]): v["sign"] for v in cells}
    crossing46 = all(signs["4_to_6", side, L] == sign for side, L, sign in
                     [("low", 4, "positive"), ("low", 6, "negative"),
                      ("high", 4, "negative"), ("high", 6, "positive")])
    crossing812 = all(signs["8_to_12", side, L] == sign for side, L, sign in
                      [("low", 8, "positive"), ("low", 12, "negative"),
                       ("high", 8, "negative"), ("high", 12, "positive")])
    fourier = [fourier_cell(4, F(16, 25), "cftp_stage4_quot_L4_r16_25_n30000.jsonl"),
               fourier_cell(6, F(16, 25), "cftp_stage4_quot_L6_r16_25_n30000.jsonl"),
               fourier_cell(8, F(34, 53), "cftp_stage5_quot_L8_r34_53_n12000.jsonl"),
               fourier_cell(12, F(34, 53), "cftp_stage5_quot_L12_r34_53_n12000.jsonl")]
    # Reuse only bytes already named by the previous independent certificates.
    repair = json.loads((ROOT / "grandcanonical_results/prg_stage4_repair_certificate.json").read_text())
    old_low = json.loads((ROOT / "grandcanonical_results/prg_covcert.json").read_text())
    old_high = json.loads((ROOT / "grandcanonical_results/prg_covcert2.json").read_text())
    prior = {(v["pair"], v["side"], v["L"]):
             (v["pilot_sha256"], v["confirm_sha256"])
             for v in repair["new_cells"][:4]}
    prior.update({("8_to_12", "low", v["L"]):
                  (v["pilot_sha256"], v["holdout_sha256"])
                  for v in old_low["cells"] if v["r"] == [7, 11]})
    prior.update({("8_to_12", "high", v["L"]):
                  (v["pilot_sha256"], v["holdout_sha256"])
                  for v in old_high["cells"]})
    assert all((v["pilot_sha256"], v["sample_sha256"]) ==
               prior[v["pair"], v["side"], v["L"]] for v in cells)
    prior_S = json.loads((ROOT / "grandcanonical_results/prg_stage5_analysis.json").read_text())
    assert all(v["sample_sha256"] == prior_S["cells"][str(v["L"])]["raw_sha256"]
               for v in fourier)
    f = {v["L"]: tuple(F(q) for q in v["S_interval"]) for v in fourier}
    quot = {"4_to_6": [enc(f[6][0] / f[4][1]), enc(f[6][1] / f[4][0])],
            "8_to_12": [enc(f[12][0] / f[8][1]), enc(f[12][1] / f[8][0])]}
    scattering = all(F(v[0]) > 1 for v in quot.values())
    result = {"method": "existing-data uniform-global-bonferroni sensitivity",
              "qualification": "The alpha reallocation was made after seeing earlier certificates; this is a post-hoc sensitivity check, not a prospectively predeclared 95% confirmatory test.",
              "conditional_on": ["ideal iid exact CFTP streams", "external Maurer-Pontil empirical-Bernstein theorem", "fixed pilot centers and thresholds"],
              "alpha": {"events": 20, "per_two_sided_interval": enc(DELTA),
                        "sum": enc(20 * DELTA), "log_bound": "ln(800)<7"},
              "crossing_cells": cells, "scattering_cells": fourier,
              "crossings": {"4_to_6": crossing46, "8_to_12": crossing812},
              "scattering_quotient_intervals": quot,
              "both_scattering_lower_gt_one": scattering,
              "all_conclusions_retain_sign": crossing46 and crossing812 and scattering,
              "code_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    OUT.write_text(json.dumps(result, indent=2) + "\n")
    for v in cells:
        print(v["pair"], v["side"], v["L"], v["sign"],
              [float(F(q)) for q in v["F_interval"]], flush=True)
    for k, v in quot.items():
        print(k, "Q_S", [float(F(q)) for q in v], flush=True)
    print("all conclusions", result["all_conclusions_retain_sign"], flush=True)


if __name__ == "__main__":
    main()
