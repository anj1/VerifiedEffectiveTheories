"""Phenomenological-RG analysis of independent CFTP replicas.

Exact integer observables and algebraic Fourier powers are retained separately
from bootstrap intervals, which are exploratory and have no finite-sample
coverage theorem. Empirical-Bernstein Binder boxes are the only sign tests.
"""
import hashlib
import json
import math
import random
import statistics
from decimal import Decimal, ROUND_CEILING, ROUND_FLOOR, getcontext
from fractions import Fraction
from pathlib import Path

getcontext().prec = 100
ROOT = Path(__file__).resolve().parent
RAW = ROOT / "grandcanonical_data" / "prg_raw"
OUT = ROOT / "grandcanonical_results" / "prg_analysis.json"
ALPHA = Decimal(1) / 20
PER_TAIL = ALPHA / 16
LOG = (Decimal(2) / PER_TAIL).ln()
PAD = Decimal("1e-9")
ROUND = Decimal("1e-12")

# Each trigonometric coefficient is (u + v sqrt(d))/2. The tables are exact.
TRIG = {
    4: (0, [2, 0, -2, 0], [0] * 4, [0, 2, 0, -2], [0] * 4),
    6: (3, [2, 1, -1, -2, -1, 1], [0] * 6,
        [0] * 6, [0, 1, 1, 0, -1, -1]),
    8: (2, [2, 0, 0, 0, -2, 0, 0, 0], [0, 1, 0, -1, 0, -1, 0, 1],
        [0, 0, 2, 0, 0, 0, -2, 0], [0, 1, 0, 1, 0, -1, 0, -1]),
    12: (3, [2, 0, 1, 0, -1, 0, -2, 0, -1, 0, 1, 0],
         [0, 1, 0, 0, 0, -1, 0, -1, 0, 0, 0, 1],
         [0, 1, 0, 2, 0, 1, 0, -1, 0, -2, 0, -1],
         [0, 0, 1, 0, 1, 0, 0, 0, -1, 0, -1, 0]),
}


def Fourier_pair(row):
    L = row["L"]
    d, cu, cv, su, sv = TRIG[L]
    P = Q = 0
    assert len(row["plane_spin_sums"]) == 3
    for plane in row["plane_spin_sums"]:
        assert len(plane) == L
        assert sum(plane) == row["magnetization_sum"]
        A = sum(x * y for x, y in zip(plane, cu))
        B = sum(x * y for x, y in zip(plane, cv))
        C = sum(x * y for x, y in zip(plane, su))
        D = sum(x * y for x, y in zip(plane, sv))
        P += A * A + d * B * B + C * C + d * D * D
        Q += 2 * (A * B + C * D)
    V = L ** 3
    # S_spin(k_min), averaged across the three symmetry-equivalent axes.
    # The denominator is 4 from trig coefficients, 3 from axis averaging, V
    # from the spin structure-factor convention.
    return P, Q, d, 12 * V


def sqrt_enclosure(d, digits=30):
    if d == 0:
        return Fraction(0), Fraction(0)
    scale = 10 ** digits
    lo = math.isqrt(d * scale * scale)
    return Fraction(lo, scale), Fraction(lo + 1, scale)


def fourier_interval(rows):
    L = rows[0]["L"]
    d = TRIG[L][0]
    P = Q = 0
    denom = None
    for row in rows:
        p, q, dd, de = Fourier_pair(row)
        assert dd == d
        if denom is None:
            denom = de
        assert de == denom
        P += p
        Q += q
    slo, shi = sqrt_enclosure(d)
    lower = Fraction(P, len(rows) * denom) + Fraction(Q, len(rows) * denom) * (slo if Q >= 0 else shi)
    upper = Fraction(P, len(rows) * denom) + Fraction(Q, len(rows) * denom) * (shi if Q >= 0 else slo)
    assert lower >= 0 and upper >= lower
    return {"exact_algebraic_mean": {"P": P, "Q": Q, "radicand": d,
                                      "denominator": len(rows) * denom},
            "interval_30_digits": [str(lower), str(upper)],
            "decimal_interval": [format(Decimal(lower.numerator) / Decimal(lower.denominator), ".25g"),
                                 format(Decimal(upper.numerator) / Decimal(upper.denominator), ".25g")],
            "point_for_exploration": float((lower + upper) / 2)}


def observations(rows):
    V = rows[0]["L"] ** 3
    result = []
    for row in rows:
        assert row["model_version"] == "grandcanonical-v4-prg"
        assert row["algorithm"] == "cftp" and row["success"]
        assert row["magnetization_sum_2"] == row["magnetization_sum"] ** 2
        assert row["magnetization_sum_4"] == row["magnetization_sum"] ** 4
        m2 = row["magnetization_sum_2"] / V ** 2
        m4 = row["magnetization_sum_4"] / V ** 4
        P, Q, d, den = Fourier_pair(row)
        sk = (P + Q * math.sqrt(d)) / den
        prior_float = sum(row["sk_axis_numerators"]) / (3 * V)
        assert abs(sk - prior_float) < 1e-8 * max(1.0, sk)
        result.append((m2, m4, row["disagreement_count"], sk))
    return result


def statistics_of(obs):
    a = statistics.mean(v[0] for v in obs)
    b = statistics.mean(v[1] for v in obs)
    D = statistics.mean(v[2] for v in obs)
    aD = statistics.mean(v[0] * v[2] for v in obs) - a * D
    bD = statistics.mean(v[1] * v[2] for v in obs) - b * D
    U = 1 - b / (3 * a * a)
    slope = -bD / (3 * a * a) + 2 * b * aD / (3 * a ** 3)
    return {"m2": a, "m4": b, "D": D, "cov_m2_D": aD,
            "cov_m4_D": bD, "U4": U, "binder_log_r_slope": slope,
            "S_spin_kmin": statistics.mean(v[3] for v in obs)}


def empirical_bernstein(values, scale, label):
    n = len(values)
    s1 = sum(values)
    s2 = sum(v * v for v in values)
    dm = Decimal(s1) / (Decimal(n) * Decimal(scale))
    dv = Decimal(n * s2 - s1 * s1) / (Decimal(n * (n - 1)) * Decimal(scale) ** 2)
    assert dv >= 0
    dn = Decimal(n)
    radius = (2 * dv * LOG / dn).sqrt() + 7 * LOG / (3 * (dn - 1))
    lo = max(Decimal(0), dm - radius - PAD).quantize(ROUND, rounding=ROUND_FLOOR)
    hi = min(Decimal(1), dm + radius + PAD).quantize(ROUND, rounding=ROUND_CEILING)
    return {"observable": label, "sample_mean": str(dm), "sample_variance": str(dv),
            "interval": [str(lo), str(hi)], "radius": str(radius)}


def binder_box(rows):
    V = rows[0]["L"] ** 3
    a = empirical_bernstein([v["magnetization_sum_2"] for v in rows], V ** 2, "m2")
    b = empirical_bernstein([v["magnetization_sum_4"] for v in rows], V ** 4, "m4")
    la, ua = map(Decimal, a["interval"])
    lb, ub = map(Decimal, b["interval"])
    if la <= 0:
        interval = None
    else:
        interval = [str((1 - ub / (3 * la * la) - PAD).quantize(ROUND, rounding=ROUND_FLOOR)),
                    str((1 - lb / (3 * ua * ua) + PAD).quantize(ROUND, rounding=ROUND_CEILING))]
    return {"m2": a, "m4": b, "binder_interval": interval}


def bootstrap_single(obs, rng, B=500):
    n = len(obs)
    estimates = []
    for _ in range(B):
        drawn = [obs[rng.randrange(n)] for _ in range(n)]
        estimates.append(statistics_of(drawn))
    return estimates


def percentile(values, p):
    a = sorted(values)
    k = (len(a) - 1) * p
    i = int(k)
    return a[i] + (a[min(i + 1, len(a) - 1)] - a[i]) * (k - i)


def load(L, a, b, n):
    path = RAW / f"cftp_prg_L{L}_r{a}_{b}_n{n}.jsonl"
    rows = [json.loads(line) for line in path.read_text().splitlines()]
    assert len(rows) == n
    assert len({row["seed"] for row in rows}) == n
    assert all(row["L"] == L and row["r_num"] == a and row["r_den"] == b for row in rows)
    return rows, path


def main():
    design = [(8, 7, 11, 1000), (12, 7, 11, 1000),
              (8, 13, 20, 1000), (12, 13, 20, 1000),
              (4, 16, 25, 2000), (6, 16, 25, 2000),
              (8, 16, 25, 1000), (12, 16, 25, 1000)]
    point = {}
    boot = {}
    sources = {}
    for L, a, b, n in design:
        rows, path = load(L, a, b, n)
        key = f"L{L}_r{a}_{b}"
        success = sum(row["success"] for row in rows)
        item = {"L": L, "r": [a, b], "n_requested": n, "n_coalesced": success,
                "max_horizon": max(row["horizon_updates"] for row in rows),
                "raw_file": str(path.relative_to(ROOT))}
        if success == n:
            obs = observations(rows)
            item.update(statistics_of(obs))
            item["Fourier_certificate"] = fourier_interval(rows)
            item["empirical_Bernstein_Binder_box"] = binder_box(rows)
            rng = random.Random(450901 + 1000 * L + 31 * a + b)
            boot[key] = bootstrap_single(obs, rng)
            item["bootstrap_percentile_95_exploratory"] = {
                field: [percentile([z[field] for z in boot[key]], .025),
                        percentile([z[field] for z in boot[key]], .975)]
                for field in ("U4", "binder_log_r_slope", "S_spin_kmin")}
        else:
            item["status"] = "censored_batch_excluded_from_inference"
        point[key] = item
        sources[str(path.relative_to(ROOT))] = hashlib.sha256(path.read_bytes()).hexdigest()
        print(key, success, "/", n, "U4", item.get("U4"), flush=True)

    comparisons = {}
    for a, b in ((7, 11), (13, 20), (16, 25)):
        p8 = point[f"L8_r{a}_{b}"]
        p12 = point[f"L12_r{a}_{b}"]
        if "U4" not in p8 or "U4" not in p12:
            continue
        u8, u12 = p8["U4"], p12["U4"]
        key = f"{a}/{b}"
        data = {"delta_U4_8_minus_12": u8 - u12}
        bi8 = p8["empirical_Bernstein_Binder_box"]["binder_interval"]
        bi12 = p12["empirical_Bernstein_Binder_box"]["binder_interval"]
        if bi8 is not None and bi12 is not None:
            data["conditional_95_familywise_difference_box"] = [
                str(Decimal(bi8[0]) - Decimal(bi12[1])),
                str(Decimal(bi8[1]) - Decimal(bi12[0]))]
        bu8, bu12 = boot[f"L8_r{a}_{b}"], boot[f"L12_r{a}_{b}"]
        diffs = [x["U4"] - y["U4"] for x, y in zip(bu8, bu12)]
        data["bootstrap_percentile_95_exploratory"] = [percentile(diffs, .025), percentile(diffs, .975)]
        comparisons[key] = data

    quotients = {}
    for L1, L2 in ((4, 6), (8, 12)):
        p, q = point[f"L{L1}_r16_25"], point[f"L{L2}_r16_25"]
        if "U4" not in p or "U4" not in q:
            continue
        s = L2 / L1
        slope_ratio = abs(q["binder_log_r_slope"]) / abs(p["binder_log_r_slope"])
        S_ratio = q["S_spin_kmin"] / p["S_spin_kmin"]
        nu = math.log(s) / math.log(slope_ratio) if slope_ratio > 1 else None
        eta = 2 - math.log(S_ratio) / math.log(s)
        bv1, bv2 = boot[f"L{L1}_r16_25"], boot[f"L{L2}_r16_25"]
        nu_boot = []
        eta_boot = []
        for x, y in zip(bv1, bv2):
            sr = abs(y["binder_log_r_slope"]) / abs(x["binder_log_r_slope"])
            if sr > 1:
                nu_boot.append(math.log(s) / math.log(sr))
            eta_boot.append(2 - math.log(y["S_spin_kmin"] / x["S_spin_kmin"]) / math.log(s))
        quotients[f"{L1}_to_{L2}_r16_25"] = {
            "status": "pseudo_crossing_proxy_not_at_certified_crossing",
            "s": s, "r": "16/25", "U4_difference": p["U4"] - q["U4"],
            "Q_U": slope_ratio, "Q_S": S_ratio,
            "nu_proxy": nu, "eta_proxy": eta,
            "bootstrap_95_exploratory": {
                "nu_proxy": [percentile(nu_boot, .025), percentile(nu_boot, .975)] if nu_boot else None,
                "eta_proxy": [percentile(eta_boot, .025), percentile(eta_boot, .975)]},
            "warning": "This is not an exponent estimate at a certified crossing; bootstrap intervals are not finite-sample confidence certificates."}

    result = {
        "experiment_id": "phenomenological_rg_v1",
        "model_version": "grandcanonical-v4-prg",
        "ensemble": "zero_field_ising_grand_canonical",
        "randomness_boundary": "Ideal independent uniform random streams are an external statistical assumption; deterministic SplitMix64 seeds are replayable but not iid randomness theorems.",
        "confidence_method": "Maurer-Pontil 2009 Theorem 4 per bounded moment, 16 tails at alpha/16 for four endpoint points; Lean binder_interval propagates the moment boxes.",
        "confidence_caveat": "Decimal ln/sqrt have 100-digit precision and 1e-9 outward guard, but transcendental rounding is not formally certified. Bootstrap intervals are exploratory only.",
        "points": point, "endpoint_comparisons": comparisons,
        "pseudo_crossing_quotients": quotients,
        "raw_sha256": sources,
        "code_sha256": {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                        for p in [ROOT / "GrandCanonicalPRG.lean", ROOT / "grandcanonical.cpp",
                                  ROOT / "prg_analyze.py"]},
    }
    OUT.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"endpoint_comparisons": comparisons,
                      "pseudo_crossing_quotients": quotients}, indent=2), flush=True)


if __name__ == "__main__":
    main()
