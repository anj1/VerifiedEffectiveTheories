"""Adaptive SW follow-up after a censored CFTP endpoint.

The new question is whether a nearby negative Binder-difference endpoint can
be both identified by fresh scouting and sampled by the existing exact kernel.
"""
import hashlib
import json
import math
import subprocess
from fractions import Fraction
from pathlib import Path

from prg_scout import estimate

ROOT = Path(__file__).resolve().parent
RAW = ROOT / "grandcanonical_data" / "prg_raw"
OUT = ROOT / "grandcanonical_results" / "prg_refine.json"
EXE = ROOT / "build" / "grandcanonical_prg"
GRID = [Fraction(7, 11), Fraction(9, 14)]
REPLICAS = 400


def main():
    result = {}
    for r in GRID:
        key = str(r)
        result[key] = {}
        for L in (8, 12):
            seed_key = f"prg-refine-v1/L={L}/r={key}"
            seed = int.from_bytes(hashlib.sha256(seed_key.encode()).digest()[:8], "little")
            path = RAW / f"sw_refine_L{L}_r{r.numerator}_{r.denominator}.jsonl"
            if not path.exists():
                subprocess.run([str(EXE), "sw", str(L), str(r.numerator), str(r.denominator),
                                str(REPLICAS), str(seed), "32", "8", str(path)], check=True)
            result[key][str(L)] = estimate(path)
        delta = result[key]["8"]["U4"] - result[key]["12"]["U4"]
        se = math.hypot(result[key]["8"]["delta_method_se_scout_only"],
                        result[key]["12"]["delta_method_se_scout_only"])
        result[key]["delta_U4_8_minus_12"] = delta
        result[key]["delta_se_scout_only"] = se
        print(f"r={key} delta={delta:+.6f} scout_se={se:.6f}", flush=True)
    payload = {
        "experiment_id": "prg-sw-refine-v1",
        "trigger": "At L=12, all five CFTP pilot streams at r=5/8 were censored at 2^25 updates; r=127/200 could not be represented by the version-3 common-denominator threshold.",
        "question": "Does a nearby rational parameter give a negative Binder difference while remaining CFTP-feasible?",
        "status": "scouting_only_not_certified",
        "grid": [str(r) for r in GRID],
        "results": result,
    }
    OUT.write_text(json.dumps(payload, indent=2) + "\n")


if __name__ == "__main__":
    main()
