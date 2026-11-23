#!/usr/bin/env python3
"""Freeze the prediction inputs and verify the local research record."""
import argparse
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
ARTIFACTS = ROOT / "artifacts"
FROZEN = ARTIFACTS / "prediction.sha256.json"
FROZEN_SHELL = ARTIFACTS / "two_shell_prediction.sha256.json"
ORIGINAL = ARTIFACTS / "five_orbital_original"
SHELL_SCRIPT = ROOT / "scripts" / "two_shell_prediction.py"
ORIGINAL_SHELL_SCRIPT = ARTIFACTS / "two_shell_original" / SHELL_SCRIPT.name
EFT_REVISION = ARTIFACTS / "five_orbital_eft.sha256.json"
ORIGINAL_SOURCES = ("Design.lean", "Effective.lean", "Prediction.lean")
CANDIDATES = [ARTIFACTS / "certificate.json", ROOT / "Grain" / "Certificate.lean"]
SHELL_CANDIDATES = [ARTIFACTS / "two_shell_full_solve.json", ROOT / "Grain" / "ShellFullData.lean"]


def closure(module):
    source = ROOT.joinpath(*module.split(".")).with_suffix(".lean")
    dependencies = re.findall(r"^import\s+(Grain\.\w+)", source.read_text(), re.M)
    return {source}.union(*(closure(name) for name in dependencies))


def five_orbital_inputs():
    return {ARTIFACTS / "design.json", ROOT / "lean-toolchain", ROOT / "lakefile.toml",
            ROOT / "lake-manifest.json"}


def original_prediction_hashes():
    shared = five_orbital_inputs() | {ROOT / "Grain" / name for name in ("Energy.lean", "Model.lean")}
    return hashes(shared) | {
        f"Grain/{name}": hashlib.sha256((ORIGINAL / name).read_bytes()).hexdigest()
        for name in ORIGINAL_SOURCES
    }


def eft_revision_inputs():
    sources = closure("Grain.ParityCancellation")
    expected = {"Energy", "Model", "Design", "RankOne", "Effective", "Prediction", "ParityCancellation"}
    if {path.stem for path in sources} != expected:
        raise ValueError("unexpected five-orbital EFT import closure")
    return sources | five_orbital_inputs()


def shell_prediction_inputs():
    sources = closure("Grain.ShellPrediction")
    expected = {"Energy", "Schur", "TwoShell", "ShellCertificate", "ShellPredictionData", "ShellPrediction"}
    if {path.stem for path in sources} != expected:
        raise ValueError("unexpected two-shell prediction import closure")
    return sources | {
        ARTIFACTS / "two_shell_prediction.json", SHELL_SCRIPT,
        ROOT / "lean-toolchain", ROOT / "lakefile.toml", ROOT / "lake-manifest.json",
    }


def hashes(paths):
    return {
        str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
        for path in sorted(paths)
    }


def verify_prediction():
    if json.loads(FROZEN.read_text()) != original_prediction_hashes():
        raise ValueError("frozen prediction inputs changed")


def verify_shell_prediction():
    recorded = json.loads(FROZEN_SHELL.read_text())
    current = hashes(shell_prediction_inputs())
    script_key = str(SHELL_SCRIPT.relative_to(ROOT))
    if current[script_key] != recorded.get(script_key) and ORIGINAL_SHELL_SCRIPT.exists():
        current[script_key] = hashlib.sha256(ORIGINAL_SHELL_SCRIPT.read_bytes()).hexdigest()
    if current != recorded:
        raise ValueError("frozen two-shell prediction inputs changed")


def audit():
    verify_prediction()
    verify_shell_prediction()
    if json.loads(EFT_REVISION.read_text()) != hashes(eft_revision_inputs()):
        raise ValueError("five-orbital EFT revision inputs changed")
    sources = closure("Grain.Certificate")
    if {path.stem for path in sources} != {"Energy", "Model", "Certify", "Certificate"}:
        raise ValueError("unexpected full-solve certificate import closure")
    shell_sources = closure("Grain.ShellFullData")
    if {path.stem for path in shell_sources} != {"Energy", "Schur", "TwoShell", "ShellCertificate", "ShellFullData"}:
        raise ValueError("unexpected two-shell full-solve certificate import closure")
    scalar_sources = closure("Grain.ScalarError")
    expected_scalar_sources = {"Energy", "Model", "Design", "RankOne", "Effective", "Prediction",
                               "ParityCancellation", "ParityMatching", "Schur", "TwoShell",
                               "ShellCertificate", "ResolventRemainder", "GroundResolvent",
                               "ScalarOccupation", "ScalarError"}
    if {path.stem for path in scalar_sources} != expected_scalar_sources:
        raise ValueError("unexpected analytic scalar budget import closure")
    for path in (ROOT / "Grain").glob("*.lean"):
        if re.search(r"\b(sorry|admit|axiom|native_decide)\b|\+native", path.read_text()):
            raise ValueError(f"proof shortcut found in {path.name}")
    print("Prediction hashes, EFT revision, and import closures verified")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("freeze", "freeze-shell", "record-eft", "verify"))
    args = parser.parse_args()
    if args.command == "freeze":
        if any(path.exists() for path in CANDIDATES):
            raise ValueError("freeze must precede full-solve artifacts")
        with FROZEN.open("x") as output:
            json.dump(original_prediction_hashes(), output, indent=2, sort_keys=True)
            output.write("\n")
    elif args.command == "freeze-shell":
        if any(path.exists() for path in SHELL_CANDIDATES):
            raise ValueError("freeze must precede the two-shell full solve")
        with FROZEN_SHELL.open("x") as output:
            json.dump(hashes(shell_prediction_inputs()), output, indent=2)
            output.write("\n")
    elif args.command == "record-eft":
        verify_prediction()
        with EFT_REVISION.open("x") as output:
            json.dump(hashes(eft_revision_inputs()), output, indent=2)
            output.write("\n")
    else:
        audit()


if __name__ == "__main__":
    main()
