"""Run the predeclared 8-to-12 CFTP quotient cells after crossing certification.

The rational parameter is selected only from finished endpoint Binder samples.
Existing raw files are never overwritten. No unsuccessful/censored draws are used.
"""
import hashlib
import json
import resource
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent
RAW = ROOT / "grandcanonical_data" / "prg_raw"
RESULT = ROOT / "grandcanonical_results"
EXE = ROOT / "build" / "grandcanonical_prg_v4_resume"


def main():
    design_path = RESULT / "prg_stage4_quotient_design.json"
    select_path = RESULT / "prg_stage4_quotient_selection.json"
    fallback_path = RESULT / "prg_stage4_fallback_design.json"
    design = json.loads(design_path.read_text())
    selection = json.loads(select_path.read_text())
    assert selection["status"] == "fallback_parameter_frozen_before_new_quotient_samples"
    fallback = json.loads(fallback_path.read_text())
    assert selection["fallback_design_sha256"] == hashlib.sha256(fallback_path.read_bytes()).hexdigest()
    assert selection["failed_refinement_certificate_sha256"] == hashlib.sha256(
        (RESULT / "prg_stage4_repair_certificate.json").read_bytes()).hexdigest()
    a, b = selection["selected_r"]
    assert 7 * b < 11 * a and 31 * a < 20 * b
    memory_limit = 6 * 1024 ** 3
    resource.setrlimit(resource.RLIMIT_AS, (memory_limit, memory_limit))
    runs = []
    for spec in fallback["new_quotient_cells"]:
        L, n = spec["L"], spec["n"]
        assert L in (8, 12) and n == 15000
        path = RAW / f"cftp_stage4_quot_L{L}_r{a}_{b}_n{n}.jsonl"
        if path.exists():
            raise FileExistsError(f"Refusing to overwrite recorded experiment: {path}")
        cmd = [str(EXE), "cftp", str(L), str(a), str(b), str(n),
               str(spec["master_seed"]), str(spec["max_cftp_updates"]),
               "0", str(path)]
        subprocess.run(cmd, check=True)
        with path.open() as file:
            rows = [json.loads(line) for line in file]
        assert len(rows) == n and len({z["seed"] for z in rows}) == n
        assert all(z["success"] and z["replica"] == i for i, z in enumerate(rows)), \
            "A censored or malformed batch cannot be used in the quotient analysis"
        runs.append({"L": L, "r": [a, b], "n": n,
                     "master_seed": spec["master_seed"],
                     "max_cftp_updates": spec["max_cftp_updates"],
                     "command": cmd, "raw_file": str(path.relative_to(ROOT)),
                     "raw_sha256": hashlib.sha256(path.read_bytes()).hexdigest()})
        print("completed quotient cell", L, a, b, n, flush=True)
    (RESULT / "prg_stage4_quotient_runs.json").write_text(json.dumps({
        "status": "predeclared_CFTP_quotient_cells_completed",
        "model_version": "grandcanonical-v4-prg",
        "executable_sha256": hashlib.sha256(EXE.read_bytes()).hexdigest(),
        "design_sha256": hashlib.sha256(design_path.read_bytes()).hexdigest(),
        "fallback_design_sha256": hashlib.sha256(fallback_path.read_bytes()).hexdigest(),
        "selection_sha256": hashlib.sha256(select_path.read_bytes()).hexdigest(),
        "memory_limit_bytes_per_process": memory_limit,
        "runs": runs,
        "randomness_boundary": "SplitMix64 streams are replayable, not iid by theorem"
    }, indent=2) + "\n")


if __name__ == "__main__":
    main()
