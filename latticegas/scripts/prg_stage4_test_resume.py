"""Byte-for-byte regression test for deterministic replica-index CFTP resume."""
import hashlib
import json
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent
EXE = ROOT / "build" / "grandcanonical_prg_v4_resume"
OUT = ROOT / "grandcanonical_results" / "prg_stage4_resume_regression.json"


def main():
    with tempfile.TemporaryDirectory(prefix="prg-resume-") as temp:
        full = Path(temp) / "full.jsonl"
        split = Path(temp) / "split.jsonl"
        common = [str(EXE), "cftp", "4", "16", "25"]
        tail = ["464160254", str(1 << 24), "0"]
        subprocess.run(common + ["40"] + tail + [str(full)], check=True)
        subprocess.run(common + ["17"] + tail + [str(split)], check=True)
        subprocess.run(common + ["23"] + tail + [str(split), "17"], check=True)
        a, b = full.read_bytes(), split.read_bytes()
        assert a == b and a.count(b"\n") == 40
        digest = hashlib.sha256(a).hexdigest()
    OUT.write_text(json.dumps({
        "status": "byte_identical_uninterrupted_and_resumed_CFTP_streams",
        "test_parameters": {"L": 4, "r": [16, 25], "master_seed": 464160254,
                            "full_n": 40, "split_n": [17, 23],
                            "max_cftp_updates": 1 << 24},
        "raw_sha256_identical": digest,
        "executable_sha256": hashlib.sha256(EXE.read_bytes()).hexdigest(),
        "limitation": "This is a finite regression test, not a universal compiler-level refinement theorem."
    }, indent=2) + "\n")
    print("resume regression byte-identical", digest, flush=True)


if __name__ == "__main__":
    main()
