"""Extend the stage-four claim graph with the one-shot negative follow-up."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
RESULT = ROOT / "grandcanonical_results"
OUT = RESULT / "prg_stage5_provenance.json"


def digest(name):
    return hashlib.sha256((RESULT / name).read_bytes()).hexdigest()


def main():
    prior = json.loads((RESULT / "prg_stage4_provenance.json").read_text())
    analysis = json.loads((RESULT / "prg_stage5_analysis.json").read_text())
    assert analysis["predeclared_bootstrap_compatibility"] == {
        "thermal": True, "correlation_scattering": False}
    nodes = prior["nodes"] + [
        {"id": "stage5_Binder_only_design", "kind": "predeclared_adaptive_design", "claim": "One correction of the sampled 8-to-12 parameter, selected only from completed Binder differences at 41/64 and 9/14; slopes and Fourier values excluded", "artifacts": ["grandcanonical_results/prg_stage5_design.json", "grandcanonical_results/prg_stage5_selection.json"], "stopping_rule": "No further parameter adjustment after this test"},
        {"id": "stage5_exact_data", "kind": "recorded_experimental_data", "claim": "Fresh 12000-draw CFTP cells each at L=8 and 12,r=34/53, all coalesced under a 6 GiB process cap", "artifacts": ["grandcanonical_results/prg_stage5_runs.json", "grandcanonical_data/prg_raw"]},
        {"id": "stage5_replay", "kind": "numerically_checked", "claim": "Selected new CFTP streams replayed independently; all 294000 recorded stage-four/five seeds are distinct", "artifact": "grandcanonical_results/prg_stage5_validation.json", "boundary": "No PRNG independence or universal compiled-code proof"},
        {"id": "refined_Binder_approximation", "kind": "exploratory_statistical_inference", "claim": "Fresh U4(8)-U4(12) point difference at 34/53 is +0.001543; exploratory bootstrap interval spans zero", "artifact": "grandcanonical_results/prg_stage5_analysis.json", "boundary": "The exact population crossing parameter is still only certified to lie in the older (7/11,20/31) bracket"},
        {"id": "stage5_S_quotients", "kind": "statistically_inferred_conditional", "claim": "Exact-algebraic S(k_min) point means and empirical-Bernstein S quotient intervals for both pairs, simultaneous conditional coverage at least 95%", "artifact": "grandcanonical_results/prg_stage5_analysis.json", "boundary": "The intervals overlap; no rigorous rejection of equal scattering dimensions"},
        {"id": "stage5_thermal_compatibility", "kind": "exploratory_statistical_inference", "claim": "Effective thermal dimensions 1.590 and 1.575 have a bootstrap difference interval spanning zero", "artifact": "grandcanonical_results/prg_stage5_analysis.json", "boundary": "Bootstrap coverage is not formal or finite-sample certified"},
        {"id": "stage5_scattering_incompatibility", "kind": "failed_predeclared_exploratory_test", "claim": "Effective scattering dimensions 1.749 and 1.933 have exploratory bootstrap larger-minus-smaller interval [0.134,0.235], excluding zero; the required two-dimension compatibility was not achieved", "artifact": "grandcanonical_results/prg_stage5_analysis.json", "boundary": "Finite-size corrections, residual crossing-location error, and bootstrap coverage remain unresolved; conservative S confidence intervals overlap"},
        {"id": "distribution_free_slope_bound", "kind": "statistically_unresolved", "claim": "Twenty bounded-observable empirical-Bernstein intervals were propagated exactly to Binder slopes; both slope quotient intervals are unresolved because conservative slope bounds cross zero", "artifacts": ["grandcanonical_results/prg_slope_bounds_design.json", "grandcanonical_results/prg_slope_bounds.json"], "boundary": "No formally certified thermal exponent interval"},
        {"id": "stage5_scattering_prediction", "kind": "conditional_prediction", "claim": "At accessible size-dependent lowest wavevectors, weak-probe intensity inherits the measured structure-factor quotient, subject to external dielectric coupling", "artifact": "grandcanonical_results/prg_stage5_analysis.json", "boundary": "No fixed-wavelength or visible-light prediction"}
    ]
    edges = prior["edges"] + [
        ["dimension_compatibility", "stage5_Binder_only_design"],
        ["failed_refinement", "stage5_Binder_only_design"],
        ["crossing_approximations", "stage5_Binder_only_design"],
        ["stage5_Binder_only_design", "stage5_exact_data"],
        ["cftp_logic", "stage5_exact_data"], ["simulator", "stage5_exact_data"],
        ["stage5_exact_data", "stage5_replay"],
        ["stage5_exact_data", "refined_Binder_approximation"],
        ["covariance_slope", "stage5_thermal_compatibility"],
        ["stage5_exact_data", "stage5_thermal_compatibility"],
        ["fourier_support", "stage5_S_quotients"],
        ["fourier_arithmetic", "stage5_S_quotients"],
        ["empirical_bernstein", "stage5_S_quotients"],
        ["stage5_exact_data", "stage5_S_quotients"],
        ["stage5_S_quotients", "stage5_scattering_incompatibility"],
        ["stage5_thermal_compatibility", "stage5_scattering_incompatibility"],
        ["empirical_bernstein", "distribution_free_slope_bound"],
        ["covariance_slope", "distribution_free_slope_bound"],
        ["stage5_exact_data", "distribution_free_slope_bound"],
        ["stage5_S_quotients", "stage5_scattering_prediction"],
        ["probe", "stage5_scattering_prediction"]
    ]
    OUT.write_text(json.dumps({
        "version": "prg-stage5-one-shot-negative-followup",
        "claim_status": "Two finite-volume crossings certified separately conditional on ideal iid streams; thermal effective dimensions exploratory-compatible; scattering effective dimensions fail the predeclared exploratory compatibility test after a Binder-only correction.",
        "confidence_accounting": "Each crossing certificate separately has conditional >=95% coverage; together >=90% by union bound. Four S boxes jointly have conditional >=95% coverage. No finite-sample bootstrap coverage or joint coverage for effective-dimension compatibility is claimed.",
        "nodes": nodes, "edges": edges,
        "stage4_graph_sha256": digest("prg_stage4_provenance.json"),
        "stage5_analysis_sha256": digest("prg_stage5_analysis.json"),
        "slope_bounds_sha256": digest("prg_slope_bounds.json")
    }, indent=2) + "\n")


if __name__ == "__main__":
    main()
