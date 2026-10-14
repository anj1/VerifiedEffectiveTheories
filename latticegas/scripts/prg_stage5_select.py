"""Freeze one Binder-only crossing-approximation correction before new draws."""
import hashlib
import json
from fractions import Fraction as F
from pathlib import Path

from prg_stage4_select_quotient import exact_thresholds_fit_u64

ROOT = Path(__file__).resolve().parent
RESULT = ROOT / "grandcanonical_results"
OUT = RESULT / "prg_stage5_selection.json"


def main():
    assert not OUT.exists(), "Refusing to change a frozen stage-five parameter"
    design_path = RESULT / "prg_stage5_design.json"
    analysis_path = RESULT / "prg_stage4_quotient_analysis.json"
    cert_path = RESULT / "prg_stage4_repair_certificate.json"
    design = json.loads(design_path.read_text())
    analysis = json.loads(analysis_path.read_text())
    cert = json.loads(cert_path.read_text())
    assert analysis["predeclared_bootstrap_compatibility"] == {
        "thermal": True, "correlation_scattering": False}
    lo, hi = F(41, 64), F(9, 14)
    dlo = F(analysis["pairs"]["8_to_12"]["point_U4_difference_small_minus_large"])
    high = {z["L"]: z for z in cert["new_cells"]
            if z["pair"] == "8_to_12" and z["side"] == "high"}
    dhi = F(high[8]["U4_point"]) - F(high[12]["U4_point"])
    assert dlo < 0 < dhi
    zero = lo - dlo * (hi - lo) / (dhi - dlo)
    oldlo, oldhi = F(7, 11), F(20, 31)
    candidates = sorted({F(p, q) for q in range(1, 81)
                         for p in range(int(lo * q), int(hi * q) + 2)
                         if lo < F(p, q) < hi and oldlo < F(p, q) < oldhi
                         and exact_thresholds_fit_u64(F(p, q))})
    assert candidates
    chosen = min(candidates, key=lambda r: (abs(r - zero), r))
    result = {
        "status": "Binder_only_refinement_frozen_before_new_exact_draws",
        "old_certified_crossing_bracket": [str(oldlo), str(oldhi)],
        "Binder_design_points": [[lo.numerator, lo.denominator],
                                 [hi.numerator, hi.denominator]],
        "Binder_difference_low": str(dlo),
        "Binder_difference_high": str(dhi),
        "linear_zero_design_only": str(zero),
        "selected_r": [chosen.numerator, chosen.denominator],
        "max_distance_to_any_crossing_in_old_bracket": str(max(chosen-oldlo, oldhi-chosen)),
        "candidate_count": len(candidates),
        "design_sha256": hashlib.sha256(design_path.read_bytes()).hexdigest(),
        "stage4_analysis_sha256": hashlib.sha256(analysis_path.read_bytes()).hexdigest(),
        "stage4_certificate_sha256": hashlib.sha256(cert_path.read_bytes()).hexdigest(),
        "source_raw_sha256": {
            str(L): analysis["cells"][str(L)]["raw_sha256"] for L in (8, 12)},
        "high_design_raw_sha256": {
            str(L): high[L]["confirm_sha256"] for L in (8, 12)},
        "code_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "slope_or_structure_factor_used_for_selection": False
    }
    OUT.write_text(json.dumps(result, indent=2) + "\n")
    print("selected Binder-only refined r", chosen,
          "linear zero", float(zero), flush=True)


if __name__ == "__main__":
    main()
