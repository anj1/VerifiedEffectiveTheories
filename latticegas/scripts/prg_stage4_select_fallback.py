"""Freeze a quotient parameter from the surviving certified 8-to-12 bracket.

This is the predeclared adaptive fallback after the 9/14 narrowing test failed.
No failed-endpoint statistics, slope values, or scattering values are read.
"""
import hashlib
import json
from fractions import Fraction as F
from pathlib import Path

from prg_stage4_select_quotient import binder, exact_thresholds_fit_u64

ROOT = Path(__file__).resolve().parent
RAW = ROOT / "grandcanonical_data" / "prg_raw"
RESULT = ROOT / "grandcanonical_results"
OUT = RESULT / "prg_stage4_quotient_selection.json"


def main():
    assert not OUT.exists(), "Refusing to overwrite a frozen parameter"
    failed_path = RESULT / "prg_stage4_repair_certificate.json"
    original_path = RESULT / "prg_covcert2.json"
    fallback_path = RESULT / "prg_stage4_fallback_design.json"
    failed = json.loads(failed_path.read_text())
    original = json.loads(original_path.read_text())
    assert failed["crossing_4_to_6_certified"]
    assert not failed["crossing_8_to_12_certified"]
    assert original["certified_8_to_12_crossing"]
    lo, hi = F(7, 11), F(20, 31)
    values, sources = {}, {}
    for r, n, prefix in ((lo, 5000, "cftp_covhold"),
                         (hi, 30000, "cftp_covstage2")):
        for L in (8, 12):
            path = RAW / f"{prefix}_L{L}_r{r.numerator}_{r.denominator}_n{n}.jsonl"
            values[(r, L)] = binder(path, L, n)
            sources[str(path.relative_to(ROOT))] = hashlib.sha256(path.read_bytes()).hexdigest()
    dlo = values[(lo, 8)] - values[(lo, 12)]
    dhi = values[(hi, 8)] - values[(hi, 12)]
    assert dlo < 0 < dhi
    zero = lo - dlo * (hi - lo) / (dhi - dlo)
    candidates = sorted({F(p, q) for q in range(1, 81)
                         for p in range(int(lo * q), int(hi * q) + 2)
                         if lo < F(p, q) < hi and exact_thresholds_fit_u64(F(p, q))})
    assert candidates
    chosen = min(candidates, key=lambda r: (abs(r - zero), r))
    result = {
        "status": "fallback_parameter_frozen_before_new_quotient_samples",
        "certified_crossing_bracket": [str(lo), str(hi)],
        "selection_rule": "Nearest representable reduced rational of denominator <=80 inside the original certified bracket, to the exact-rational linear zero of the original endpoint Binder point differences; ties to smaller rational.",
        "delta_U4_low": str(dlo), "delta_U4_high": str(dhi),
        "linear_zero_design_only": str(zero),
        "selected_r": [chosen.numerator, chosen.denominator],
        "max_distance_to_any_crossing_in_bracket": str(max(chosen - lo, hi - chosen)),
        "candidate_count": len(candidates),
        "source_sha256": sources,
        "old_crossing_certificate_sha256": hashlib.sha256(original_path.read_bytes()).hexdigest(),
        "failed_refinement_certificate_sha256": hashlib.sha256(failed_path.read_bytes()).hexdigest(),
        "fallback_design_sha256": hashlib.sha256(fallback_path.read_bytes()).hexdigest(),
        "code_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "failed_9_14_endpoint_used_for_selection": False
    }
    OUT.write_text(json.dumps(result, indent=2) + "\n")
    print("fallback selected r", chosen, "linear zero", float(zero), flush=True)


if __name__ == "__main__":
    main()
