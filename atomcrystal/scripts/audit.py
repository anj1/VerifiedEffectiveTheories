#!/usr/bin/env python3
"""Read-only provenance and trust audit. Numeric programs are not verifiers.

The import checks establish dependency separation, not real-world chronology.
Run Lean's independent checker separately as documented in README.md.
"""
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def closure(module, seen=None):
    seen = set() if seen is None else seen
    if module in seen or not module.startswith("VerifiedPhysics"):
        return seen
    seen.add(module)
    source = ROOT.joinpath(*module.split(".")).with_suffix(".lean").read_text()
    for dependency in re.findall(r"^import\s+(VerifiedPhysics[\w.]*)", source, re.M):
        closure(dependency, seen)
    return seen


def main():
    prediction = closure("VerifiedPhysics.Effective.MaxwellPrediction")
    forbidden = [m for m in prediction if any(part in m for part in
                 ("MaxwellSlab", "Certificates", "CrossScale", "Experiments"))]
    if forbidden:
        raise SystemExit(f"prediction depends on lower surface test: {forbidden}")
    certificate = closure("VerifiedPhysics.Certificates.MaxwellBounds")
    forbidden = [m for m in certificate if ".Effective." in m or ".Bulk." in m]
    if forbidden:
        raise SystemExit(f"surface certificate imports effective law: {forbidden}")
    scattering_prediction = closure("VerifiedPhysics.Prediction.FrozenScatteringPrediction")
    forbidden = [m for m in scattering_prediction if any(part in m for part in
                 (".Experiments.", ".Certificates.", ".CrossScale.", "MaxwellSlab", "MaxwellHamiltonian"))]
    if forbidden:
        raise SystemExit(f"scattering prediction depends on validation: {forbidden}")
    scattering_certificate = closure("VerifiedPhysics.Experiments.ScatteringCertificate")
    forbidden = [m for m in scattering_certificate if any(part in m for part in
                 (".Effective.", ".Prediction.", ".Bulk.", ".Certificates.", ".CrossScale."))]
    if forbidden:
        raise SystemExit(f"driven certificate imports a theory or prior mode result: {forbidden}")
    for path in ROOT.joinpath("VerifiedPhysics").rglob("*.lean"):
        text = path.read_text()
        if re.search(r"\b(sorry|admit|axiom|native_decide)\b|\+native|native\s*:=\s*true", text):
            raise SystemExit(f"unapproved trust escape in {path.relative_to(ROOT)}")
    checked = 0
    preserved_baseline = []
    for line in ROOT.joinpath("artifacts/source_revision.sha256").read_text().splitlines():
        digest, name = line.split("  ", 1)
        actual = hashlib.sha256(ROOT.joinpath(name).read_bytes()).hexdigest()
        if digest != actual:
            original = ROOT / "artifacts/scattering_provenance/baseline_sources" / name
            if not original.exists() or hashlib.sha256(original.read_bytes()).hexdigest() != digest:
                raise SystemExit(f"source snapshot mismatch without preserved original: {name}")
            preserved_baseline.append(name)
        checked += 1
    snapshots = ROOT / "artifacts/scattering_provenance"
    for stage in ("baseline", "prediction", "result"):
        snapshot = json.loads((snapshots / f"{stage}.json").read_text())
        for name, digest in snapshot["sha256"].items():
            target = snapshots / "baseline_sources" / name if stage == "baseline" else ROOT / name
            if hashlib.sha256(target.read_bytes()).hexdigest() != digest:
                raise SystemExit(f"{stage} hash mismatch: {name}")
    final_sources = json.loads((snapshots / "result.json").read_text())["sha256"]
    for path in ROOT.joinpath("VerifiedPhysics").rglob("*.lean"):
        if str(path.relative_to(ROOT)) not in final_sources:
            raise SystemExit(f"Unhashed final Lean source: {path}")
    headline = "VerifiedPhysics/Final/MainTheorem.lean"
    old_body = (snapshots / "baseline_sources" / headline).read_text().split(
        "namespace VerifiedPhysics\n", 1)[1].rsplit("\nend VerifiedPhysics", 1)[0].strip()
    retained_body = (ROOT / headline).read_text().split(
        "namespace VerifiedPhysics\n", 1)[1].split("\nopen GratingExperiment in", 1)[0].strip()
    if old_body != retained_body:
        raise SystemExit("Earlier headline theorems were rewritten")
    print(json.dumps({
        "source_hashes_checked": checked,
        "modified_legacy_sources_preserved_verbatim": preserved_baseline,
        "prediction_imports_no_surface_test": True,
        "surface_certificate_imports_no_effective_law": True,
        "scattering_prediction_imports_no_validation": True,
        "driven_certificate_imports_no_theory_or_eigenmode_result": True,
        "all_three_scattering_stage_snapshots": "passed",
        "earlier_headline_theorems_preserved_verbatim": True,
        "trust_escape_scan": "passed",
        "chronology": "recorded by execution artifacts; not a mathematical theorem",
        "proof_verifier": "run lake env leanchecker VerifiedPhysics.Final.MainTheorem"
    }, indent=2))


if __name__ == "__main__":
    main()
