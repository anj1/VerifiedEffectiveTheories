"""Resume an externally interrupted, fixed-count CFTP experiment exactly.

The original interrupted file is preserved. Only complete JSONL rows are
copied byte-for-byte to a new artifact; the unfinished trailing record is
excluded. Replica indices and deterministic seeds are checked before the
unchanged remaining indices are generated. No sample statistic is inspected
to choose the resume point or sample count.
"""
import hashlib
import json
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent
RAW = ROOT / "grandcanonical_data" / "prg_raw"
RESULT = ROOT / "grandcanonical_results"
ORIGINAL = RAW / "cftp_stage4_confirm_L12_r9_14_n40000.jsonl"
RECOVERED = RAW / "cftp_stage4_confirm_L12_r9_14_n40000_recovered.jsonl"
EXE = ROOT / "build" / "grandcanonical_prg_v4_resume"
OUT = RESULT / "prg_stage4_endpoint_recovery.json"
MASTER = 812090142
TARGET = 40000
MASK = (1 << 64) - 1
GOLDEN = 0x9e3779b97f4a7c15


def mix(z):
    z = ((z ^ (z >> 30)) * 0xbf58476d1ce4e5b9) & MASK
    z = ((z ^ (z >> 27)) * 0x94d049bb133111eb) & MASK
    return z ^ (z >> 31)


def checked_prefix(data):
    last_newline = data.rfind(b"\n")
    assert last_newline >= 0
    prefix = data[:last_newline + 1]
    tail = data[last_newline + 1:]
    assert tail and b"\n" not in tail  # preserve an incomplete last record
    lines = prefix.splitlines()
    for i, line in enumerate(lines):
        row = json.loads(line)
        assert row["replica"] == i
        assert row["seed"] == mix(MASTER ^ ((GOLDEN * (i + 1)) & MASK))
        assert row["model_version"] == "grandcanonical-v4-prg"
        assert row["algorithm"] == "cftp" and row["success"]
        assert (row["L"], row["r_num"], row["r_den"]) == (12, 9, 14)
    assert 0 < len(lines) < TARGET
    return prefix, len(lines), tail


def main():
    assert not RECOVERED.exists(), "Refusing to overwrite any recovery artifact"
    assert not OUT.exists(), "Refusing to overwrite the recovery manifest"
    original = ORIGINAL.read_bytes()
    prefix, first_missing, unfinished = checked_prefix(original)
    with RECOVERED.open("xb") as file:
        file.write(prefix)
    command = [str(EXE), "cftp", "12", "9", "14", str(TARGET - first_missing),
               str(MASTER), str(1 << 26), "0", str(RECOVERED), str(first_missing)]
    print("resuming complete replica prefix", first_missing,
          "remaining", TARGET - first_missing, flush=True)
    subprocess.run(command, check=True)
    recovered = RECOVERED.read_bytes()
    assert recovered.startswith(prefix) and recovered.endswith(b"\n")
    assert recovered.count(b"\n") == TARGET
    for i, line in enumerate(recovered.splitlines()):
        row = json.loads(line)
        assert row["replica"] == i
        assert row["seed"] == mix(MASTER ^ ((GOLDEN * (i + 1)) & MASK))
        assert row["success"] and row["model_version"] == "grandcanonical-v4-prg"
        assert (row["L"], row["r_num"], row["r_den"]) == (12, 9, 14)
    OUT.write_text(json.dumps({
        "status": "fixed_count_completed_after_external_interruption",
        "original_file": str(ORIGINAL.relative_to(ROOT)),
        "original_sha256": hashlib.sha256(original).hexdigest(),
        "complete_prefix_rows": first_missing,
        "unfinished_original_tail_bytes": len(unfinished),
        "recovered_file": str(RECOVERED.relative_to(ROOT)),
        "recovered_sha256": hashlib.sha256(recovered).hexdigest(),
        "target_rows": TARGET,
        "resume_command": command,
        "resume_executable_sha256": hashlib.sha256(EXE.read_bytes()).hexdigest(),
        "method": "Byte-identical completed prefix plus fresh computation of exactly the missing replica indices with the unchanged seed rule; original file untouched.",
        "randomness_boundary": "Conditional on ideal iid streams; deterministic PRNG replay does not prove independence."
    }, indent=2) + "\n")
    print("recovered exact fixed-count file", TARGET, flush=True)


if __name__ == "__main__":
    main()
