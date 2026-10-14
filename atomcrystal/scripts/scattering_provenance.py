#!/usr/bin/env python3
"""Append-only stage creation and read-only verification of source snapshots.

Hashes establish identity, not an externally timestamped commitment. Existing
stage files cannot be replaced by this program. Prediction closure is audited
separately; snapshot the full baseline before changing its headline theorem.
"""
import argparse
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("stage", choices=["baseline", "prediction", "result", "verify"])
    args = parser.parse_args()
    folder = ROOT / "artifacts/scattering_provenance"
    if args.stage == "verify":
        for path in sorted(folder.glob("*.json")):
            data = json.loads(path.read_text())
            for name, expected in data["sha256"].items():
                # Baseline originals are retained verbatim in this snapshot.
                target = folder / "baseline_sources" / name if data["stage"] == "baseline" else ROOT / name
                assert digest(target) == expected, (path.name, name)
            print(f"{path.name}: {len(data['sha256'])} identities verified")
        return
    folder.mkdir(exist_ok=True)
    out = folder / f"{args.stage}.json"
    if out.exists():
        raise SystemExit(f"Refusing to replace frozen stage {out}")
    if args.stage == "baseline":
        paths = sorted(ROOT.glob("VerifiedPhysics/**/*.lean"))
        paths = [p for p in paths if "/Prediction/" not in str(p)]
        paths += [ROOT / "artifacts/source_revision.sha256", ROOT / "README.md"]
        for path in paths:
            target = folder / "baseline_sources" / path.relative_to(ROOT)
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(path.read_bytes())
    elif args.stage == "prediction":
        from audit import closure
        paths = [ROOT.joinpath(*m.split(".")).with_suffix(".lean")
                 for m in sorted(closure("VerifiedPhysics.Prediction.FrozenScatteringPrediction"))]
        paths += [ROOT / "artifacts/scattering_design.json", folder / "baseline.json"]
    else:
        paths = sorted(ROOT.glob("VerifiedPhysics/**/*.lean"))
        paths += sorted(ROOT.glob("scripts/*.py"))
        paths += [ROOT / "artifacts/scattering_certificate.json", folder / "prediction.json",
                  ROOT / "README.md", ROOT / "artifacts/scattering_report.md",
                  ROOT / "artifacts/scattering_verification.json", ROOT / "VerifiedPhysics.lean",
                  ROOT / "lean-toolchain", ROOT / "lakefile.toml", ROOT / "lake-manifest.json"]
    data = {"stage": args.stage, "recorded_utc": datetime.now(timezone.utc).isoformat(),
            "sha256": {str(p.relative_to(ROOT)): digest(p) for p in paths}}
    with out.open("x") as f:
        json.dump(data, f, indent=2)
        f.write("\n")
    print(f"Frozen {args.stage}: {len(paths)} source identities")


if __name__ == "__main__":
    main()
