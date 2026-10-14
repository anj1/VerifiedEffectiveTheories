"""Machine-readable dependency graph for the stage-four RG claims."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
RESULT = ROOT / "grandcanonical_results"
OUT = RESULT / "prg_stage4_provenance.json"


def sha(path):
    return hashlib.sha256((ROOT / path).read_bytes()).hexdigest()


def main():
    cert = json.loads((RESULT / "prg_stage4_repair_certificate.json").read_text())
    quot = json.loads((RESULT / "prg_stage4_quotient_analysis.json").read_text())
    selection = json.loads((RESULT / "prg_stage4_quotient_selection.json").read_text())
    assert cert["crossing_4_to_6_certified"] and not cert["crossing_8_to_12_certified"]
    assert selection["status"] == "fallback_parameter_frozen_before_new_quotient_samples"
    compatible = quot["predeclared_bootstrap_compatibility"]
    nodes = [
        {"id": "ising_law", "kind": "assumed", "claim": "Finite zero-field cubic Ising Gibbs law with rational weight r^D", "artifact": "GrandCanonical.lean"},
        {"id": "heatbath", "kind": "formally_proved", "claim": "Concrete six-neighbour conditional, monotonicity, detailed balance, stationarity", "artifact": "GrandCanonicalPRG.lean"},
        {"id": "cftp_logic", "kind": "formally_proved_conditional", "claim": "All-minus/all-plus coalescence implies all-start coalescence; stationary output given an ideal stationary reference past", "artifact": "GrandCanonical.lean", "boundary": "Construction of a two-sided stationary reference process remains an explicit premise"},
        {"id": "ideal_iid", "kind": "assumed", "claim": "Independent unbiased random instructions for independent CFTP replicas", "boundary": "SplitMix64 is deterministic and does not prove iid"},
        {"id": "simulator", "kind": "numerically_checked", "claim": "Exact integer heat-bath thresholds and selected independent Python replay", "artifacts": ["grandcanonical.cpp", "prg_stage4_validate.py", "grandcanonical_results/prg_stage4_validation.json"], "boundary": "No universal C++ refinement theorem"},
        {"id": "recovery", "kind": "numerically_checked", "claim": "Byte-identical 33269-record prefix, deterministic continuation to predeclared 40000; original interrupted file retained", "artifact": "grandcanonical_results/prg_stage4_endpoint_recovery.json"},
        {"id": "endpoint_data", "kind": "recorded_experimental_data", "claim": "Independent fixed-count CFTP Binder endpoint cells across two size pairs", "artifact": "grandcanonical_data/prg_raw", "hash_manifest": "grandcanonical_results/prg_stage4_repair_certificate.json"},
        {"id": "empirical_bernstein", "kind": "external_statistical_theorem", "claim": "Bounded iid empirical-Bernstein coverage and union bound", "source": "https://www.cs.mcgill.ca/~colt2009/papers/012.pdf", "boundary": "The concentration theorem is not yet formalized in Lean"},
        {"id": "binder_sign_logic", "kind": "formally_proved", "claim": "Centered-observable interval propagation and finite-volume crossing from opposite endpoint signs", "artifact": "GrandCanonicalPRG.lean"},
        {"id": "small_crossing", "kind": "statistically_inferred_conditional", "claim": "There is a 4-to-6 finite-volume Binder crossing in (12/19,11/17), with conditional familywise coverage at least 95%", "artifact": "grandcanonical_results/prg_stage4_repair_certificate.json"},
        {"id": "failed_refinement", "kind": "statistically_unresolved", "claim": "At 9/14 the L=12 Binder sign interval contains zero; (7/11,9/14) is not a certified 8-to-12 bracket", "artifact": "grandcanonical_results/prg_stage4_repair_certificate.json"},
        {"id": "large_crossing", "kind": "statistically_inferred_conditional", "claim": "The previously certified 8-to-12 crossing remains in (7/11,20/31), with conditional familywise coverage at least 95%", "artifact": "grandcanonical_results/prg_covcert2.json"},
        {"id": "crossing_approximations", "kind": "predeclared_design", "claim": "4-to-6 r=16/25 and 8-to-12 fallback rational selected using certified endpoint Binder point differences alone", "artifacts": ["grandcanonical_results/prg_stage4_quotient_design.json", "grandcanonical_results/prg_stage4_fallback_design.json", "grandcanonical_results/prg_stage4_quotient_selection.json"], "boundary": "Brackets locate a crossing but do not prove that the sampled rational equals it"},
        {"id": "quotient_data", "kind": "recorded_experimental_data", "claim": "Fresh fixed-count exact-CFTP samples at pair-specific crossing approximations", "artifact": "grandcanonical_results/prg_stage4_quotient_runs.json"},
        {"id": "covariance_slope", "kind": "formally_proved", "claim": "d E[f]/d log r = Cov(f,D), including exact Binder-slope formula", "artifact": "GrandCanonicalPRG.lean"},
        {"id": "fourier_support", "kind": "formally_proved", "claim": "Each normalized finite spin Fourier power lies in [0,V]", "artifact": "GrandCanonicalPRG.lean"},
        {"id": "fourier_arithmetic", "kind": "numerically_certified", "claim": "Lowest-mode powers from integer plane sums with exact quadratic-algebraic rational enclosures", "artifact": "prg_stage4_quotient_analyze.py", "boundary": "Trigonometric lookup tables are not yet Lean-proved"},
        {"id": "S_quotients", "kind": "statistically_inferred_conditional", "claim": "Two finite-volume scattering quotients have simultaneous 95% exact-rational empirical-Bernstein bounds under ideal iid CFTP and the external theorem", "artifact": "grandcanonical_results/prg_stage4_quotient_analysis.json"},
        {"id": "thermal_dimensions", "kind": "exploratory_statistical_inference", "claim": "Exact-rational slope point quotients transformed by floating logarithms; bootstrap thermal-dimension intervals are exploratory, not finite-sample certified", "artifact": "grandcanonical_results/prg_stage4_quotient_analysis.json"},
        {"id": "dimension_compatibility", "kind": "exploratory_statistical_inference" if all(compatible.values()) else "failed_predeclared_exploratory_test", "claim": "Predeclared bootstrap between-pair thermal and scattering dimension differences include zero" if all(compatible.values()) else "At least one predeclared bootstrap between-pair dimension interval excludes zero; compatibility was not established", "artifact": "grandcanonical_results/prg_stage4_quotient_analysis.json", "boundary": "No finite-sample bootstrap coverage theorem; unresolved finite-size and crossing-location corrections"},
        {"id": "probe", "kind": "assumed", "claim": "Linear density-dielectric coupling and weak-scattering approximation", "artifact": "LatticeGasScattering.lean"},
        {"id": "scattering_prediction", "kind": "conditional_prediction", "claim": "At accessible size-dependent k_min, probe intensity quotient inherits the measured structure-factor quotient", "artifact": "grandcanonical_results/prg_stage4_quotient_analysis.json", "boundary": "Not a fixed-wavelength or literal visible-light prediction"}
    ]
    edges = [
        ["ising_law", "heatbath"], ["heatbath", "cftp_logic"],
        ["ideal_iid", "cftp_logic"], ["cftp_logic", "endpoint_data"],
        ["simulator", "endpoint_data"], ["recovery", "endpoint_data"],
        ["endpoint_data", "small_crossing"], ["endpoint_data", "failed_refinement"],
        ["empirical_bernstein", "small_crossing"], ["binder_sign_logic", "small_crossing"],
        ["large_crossing", "crossing_approximations"], ["small_crossing", "crossing_approximations"],
        ["failed_refinement", "crossing_approximations"], ["crossing_approximations", "quotient_data"],
        ["cftp_logic", "quotient_data"], ["simulator", "quotient_data"],
        ["covariance_slope", "thermal_dimensions"], ["quotient_data", "thermal_dimensions"],
        ["fourier_support", "S_quotients"], ["fourier_arithmetic", "S_quotients"],
        ["quotient_data", "S_quotients"], ["empirical_bernstein", "S_quotients"],
        ["thermal_dimensions", "dimension_compatibility"], ["S_quotients", "dimension_compatibility"],
        ["S_quotients", "scattering_prediction"], ["probe", "scattering_prediction"]
    ]
    OUT.write_text(json.dumps({
        "version": "prg-stage4",
        "joint_crossing_coverage_conditional_lower_bound": 0.90,
        "S_quotient_familywise_coverage_conditional_lower_bound": 0.95,
        "no_joint_coverage_claim_for_bootstrap_dimensions": True,
        "nodes": nodes, "edges": edges,
        "certificate_sha256": sha("grandcanonical_results/prg_stage4_repair_certificate.json"),
        "analysis_sha256": sha("grandcanonical_results/prg_stage4_quotient_analysis.json")
    }, indent=2) + "\n")


if __name__ == "__main__":
    main()
