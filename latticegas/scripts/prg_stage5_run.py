"""Run the one predeclared Binder-only crossing-approximation refinement."""
import hashlib
import json
import resource
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent
RESULT = ROOT / "grandcanonical_results"
RAW = ROOT / "grandcanonical_data" / "prg_raw"
EXE = ROOT / "build" / "grandcanonical_prg_v4_resume"
OUT = RESULT / "prg_stage5_runs.json"


def main():
    assert not OUT.exists(), "Refusing to overwrite a completed run manifest"
    design_path = RESULT / "prg_stage5_design.json"
    selection_path = RESULT / "prg_stage5_selection.json"
    design = json.loads(design_path.read_text())
    selection = json.loads(selection_path.read_text())
    assert selection["status"] == "Binder_only_refinement_frozen_before_new_exact_draws"
    assert selection["design_sha256"] == hashlib.sha256(design_path.read_bytes()).hexdigest()
    a, b = selection["selected_r"]
    memory = design["memory_limit_bytes_per_process"]
    resource.setrlimit(resource.RLIMIT_AS, (memory, memory))
    runs = []
    for spec in design["fresh_exact_cells"]:
        L, n = spec["L"], spec["n"]
        assert L in (8, 12) and n == 12000
        path = RAW / f"cftp_stage5_quot_L{L}_r{a}_{b}_n{n}.jsonl"
        assert not path.exists(), "Refusing to overwrite raw exact-sample data"
        command = [str(EXE), "cftp", str(L), str(a), str(b), str(n),
                   str(spec["master_seed"]), str(spec["max_cftp_updates"]),
                   "0", str(path)]
        subprocess.run(command, check=True)
        with path.open() as file:
            rows = [json.loads(line) for line in file]
        assert len(rows) == n and len({z["seed"] for z in rows}) == n
        assert all(z["success"] and z["replica"] == i for i, z in enumerate(rows))
        runs.append({"L": L, "r": [a, b], "n": n,
                     "master_seed": spec["master_seed"],
                     "max_cftp_updates": spec["max_cftp_updates"],
                     "raw_file": str(path.relative_to(ROOT)),
                     "raw_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
                     "command": command})
        print("completed stage-five exact quotient cell", L, n, flush=True)
    OUT.write_text(json.dumps({
        "status": "both_fresh_fixed_count_exact_quotient_cells_completed",
        "design_sha256": hashlib.sha256(design_path.read_bytes()).hexdigest(),
        "selection_sha256": hashlib.sha256(selection_path.read_bytes()).hexdigest(),
        "executable_sha256": hashlib.sha256(EXE.read_bytes()).hexdigest(),
        "memory_limit_bytes_per_process": memory,
        "runs": runs,
        "randomness_boundary": "SplitMix64 outputs are replayable; iid equilibrium law is conditional on ideal independent random instructions"
    }, indent=2) + "\n")


if __name__ == "__main__":
    main()
