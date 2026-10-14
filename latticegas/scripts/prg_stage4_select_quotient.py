"""Freeze the 8-to-12 quotient parameter from completed Binder endpoints.

No slope or structure-factor values are read. The selection precedes every
new quotient sample at the selected parameter.
"""
import hashlib
import json
import math
from fractions import Fraction as F
from pathlib import Path

ROOT = Path(__file__).resolve().parent
RAW = ROOT / "grandcanonical_data" / "prg_raw"
OUT = ROOT / "grandcanonical_results" / "prg_stage4_quotient_selection.json"


def binder(path, L, n):
    rows = [json.loads(line) for line in path.read_text().splitlines()]
    assert len(rows) == n and all(z["success"] for z in rows)
    V = L ** 3
    a = sum((F(z["magnetization_sum_2"], V ** 2) for z in rows), F(0)) / n
    b = sum((F(z["magnetization_sum_4"], V ** 4) for z in rows), F(0)) / n
    return 1 - b / (3 * a ** 2)


def exact_thresholds_fit_u64(r):
    a, b = r.numerator, r.denominator
    limit = 2 ** 64 - 1
    common = 1
    for k in range(7):
        num = a ** (6 - k) * b ** k
        other = a ** k * b ** (6 - k)
        den = num + other
        if max(num, other, den) > limit:
            return False
        common = math.lcm(common, den // math.gcd(num, den))
        if common > limit:
            return False
    return True


def main():
    cert_path = ROOT / "grandcanonical_results/prg_stage4_repair_certificate.json"
    cert = json.loads(cert_path.read_text())
    assert cert["crossing_8_to_12_certified"]
    lo, hi = F(7, 11), F(9, 14)
    sources = {}
    values = {}
    for r, n, prefix in ((lo, 5000, "cftp_covhold"),
                         (hi, 40000, "cftp_stage4_confirm")):
        for L in (8, 12):
            suffix = "_recovered" if r == hi and L == 12 else ""
            path = RAW / f"{prefix}_L{L}_r{r.numerator}_{r.denominator}_n{n}{suffix}.jsonl"
            values[(r, L)] = binder(path, L, n)
            sources[str(path.relative_to(ROOT))] = hashlib.sha256(path.read_bytes()).hexdigest()
    dlo = values[(lo, 8)] - values[(lo, 12)]
    dhi = values[(hi, 8)] - values[(hi, 12)]
    assert dlo < 0 < dhi
    linear_zero = lo - dlo * (hi - lo) / (dhi - dlo)
    candidates = sorted({F(p, q) for q in range(1, 81)
                         for p in range(int(lo * q), int(hi * q) + 2)
                         if lo < F(p, q) < hi and exact_thresholds_fit_u64(F(p, q))})
    assert candidates
    chosen = min(candidates, key=lambda r: (abs(r - linear_zero), r))
    result = {"status": "parameter_frozen_before_new_quotient_samples",
              "selection_rule": "Nearest reduced rational strictly within the certified bracket, denominator <=80 and common heat-bath denominator fitting uint64, to the exact-rational linear zero of two Binder point differences; ties to smaller rational. No quotient observable used.",
              "low_r": str(lo), "high_r": str(hi),
              "delta_U4_low": str(dlo), "delta_U4_high": str(dhi),
              "linear_zero_design_only": str(linear_zero),
              "selected_r": [chosen.numerator, chosen.denominator],
              "max_distance_to_any_crossing_in_bracket": str(max(chosen - lo, hi - chosen)),
              "candidate_count": len(candidates),
              "source_sha256": sources,
              "crossing_certificate_sha256": hashlib.sha256(cert_path.read_bytes()).hexdigest(),
              "code_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    OUT.write_text(json.dumps(result, indent=2) + "\n")
    print("selected 8-to-12 quotient r", chosen,
          "linear design zero", float(linear_zero), flush=True)


if __name__ == "__main__":
    main()
