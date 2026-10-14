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
    for path in ROOT.joinpath("VerifiedPhysics").rglob("*.lean"):
        text = path.read_text()
        if re.search(r"\b(sorry|admit|axiom|native_decide)\b|\+native|native\s*:=\s*true", text):
            raise SystemExit(f"unapproved trust escape in {path.relative_to(ROOT)}")
    checked = 0
    for line in ROOT.joinpath("artifacts/source_revision.sha256").read_text().splitlines():
        digest, name = line.split("  ", 1)
        actual = hashlib.sha256(ROOT.joinpath(name).read_bytes()).hexdigest()
        if digest != actual:
            raise SystemExit(f"source snapshot mismatch: {name}")
        checked += 1
    print(json.dumps({
        "source_hashes_checked": checked,
        "prediction_imports_no_surface_test": True,
        "surface_certificate_imports_no_effective_law": True,
        "trust_escape_scan": "passed",
        "chronology": "recorded by execution artifacts; not a mathematical theorem",
        "proof_verifier": "run lake env leanchecker VerifiedPhysics.Final.MainTheorem"
    }, indent=2))


if __name__ == "__main__":
    main()
