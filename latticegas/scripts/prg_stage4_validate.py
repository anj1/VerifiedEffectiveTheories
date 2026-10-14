"""Selected independent Python replays of stage-four CFTP output.

This checks implementation agreement for chosen streams. It is not a proof
of universal C++ refinement or of stochastic independence of SplitMix64.
"""
import hashlib
import json
from pathlib import Path

from prg_validate import replay

ROOT = Path(__file__).resolve().parent
RAW = ROOT / "grandcanonical_data" / "prg_raw"
OUT = ROOT / "grandcanonical_results" / "prg_stage4_validation.json"


def main():
    cert = json.loads((ROOT / "grandcanonical_results" /
                       "prg_stage4_repair_certificate.json").read_text())
    quot = json.loads((ROOT / "grandcanonical_results" /
                       "prg_stage4_quotient_analysis.json").read_text())
    names = [Path(z["confirm_file"]).name for z in cert["new_cells"]]
    names += [Path(z["raw_file"]).name for z in quot["cells"].values()]
    checks, hashes, seen_seeds = [], {}, set()
    for name in names:
        path = RAW / name
        with path.open() as file:
            first = json.loads(next(file))
            seed = first["seed"]
            assert seed not in seen_seeds
            seen_seeds.add(seed)
            rows = 1
            for line in file:
                seed = json.loads(line)["seed"]
                assert seed not in seen_seeds
                seen_seeds.add(seed)
                rows += 1
        checks.append(replay(first))
        hashes[str(path.relative_to(ROOT))] = hashlib.sha256(path.read_bytes()).hexdigest()
        print("replayed", name, first["horizon_updates"], "rows", rows, flush=True)
    assert len(checks) == 10
    OUT.write_text(json.dumps({
        "status": "selected_CFTP_stream_replay_matches_recorded_state_and_observables",
        "scope": "first replica of each of six new crossing cells and four quotient cells",
        "checks": checks,
        "distinct_recorded_seeds_across_all_ten_new_cells": len(seen_seeds),
        "raw_sha256": hashes,
        "limitation": "Selected deterministic replays do not prove universal C++ refinement or PRNG independence."
    }, indent=2) + "\n")


if __name__ == "__main__":
    main()
