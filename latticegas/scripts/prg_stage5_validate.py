"""Selected replay and deterministic seed-domain audit for final exact cells."""
import hashlib
import json
from pathlib import Path

from prg_validate import replay

ROOT = Path(__file__).resolve().parent
RAW = ROOT / "grandcanonical_data" / "prg_raw"
RESULT = ROOT / "grandcanonical_results"
OUT = RESULT / "prg_stage5_validation.json"


def main():
    runs = json.loads((RESULT / "prg_stage5_runs.json").read_text())
    prior = json.loads((RESULT / "prg_stage4_validation.json").read_text())
    seen = set()
    old_paths = list(prior["raw_sha256"])
    new_paths = [z["raw_file"] for z in runs["runs"]]
    checks, hashes = [], {}
    for relative in old_paths + new_paths:
        path = ROOT / relative
        with path.open() as file:
            first = json.loads(next(file))
            assert first["seed"] not in seen
            seen.add(first["seed"])
            for line in file:
                seed = json.loads(line)["seed"]
                assert seed not in seen
                seen.add(seed)
        hashes[relative] = hashlib.sha256(path.read_bytes()).hexdigest()
        if relative in new_paths:
            checks.append(replay(first))
            print("replayed new stage-five cell", relative, flush=True)
        else:
            assert hashes[relative] == prior["raw_sha256"][relative]
    assert len(checks) == 2
    OUT.write_text(json.dumps({
        "status": "selected_new_streams_replayed_and_all_recorded_seeds_distinct",
        "new_replay_checks": checks,
        "total_distinct_seeds_across_stage4_and_stage5": len(seen),
        "new_raw_sha256": {p: hashes[p] for p in new_paths},
        "earlier_validation_sha256": hashlib.sha256(
            (RESULT / "prg_stage4_validation.json").read_bytes()).hexdigest(),
        "limitation": "Deterministic non-overlap and selected replay do not establish iid randomness or universal compiled-code refinement."
    }, indent=2) + "\n")


if __name__ == "__main__":
    main()
