"""Locate the five-orbital certificate inputs and check the frozen design."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ARTIFACTS = ROOT / "artifacts"
CANDIDATES = [ARTIFACTS / "certificate.json", ROOT / "Grain" / "Certificate.lean"]


def verify_prediction():
    recorded = json.loads((ARTIFACTS / "prediction.sha256.json").read_text())
    design = (ARTIFACTS / "design.json").read_bytes()
    if hashlib.sha256(design).hexdigest() != recorded["artifacts/design.json"]:
        raise ValueError("frozen five-orbital design changed")
