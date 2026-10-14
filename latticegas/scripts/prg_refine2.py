"""Second adaptive scout: find a positive-sign endpoint nearer the crossing.

The initial 13/20 endpoint is easy to sample but has a small second moment at
L=12; conservative Binder bounds consequently require too many samples.
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
OUT = ROOT / "grandcanonical_results" / "prg_refine2.json"
EXE = ROOT / "build" / "grandcanonical_prg_v4"
GRID = [Fraction(20, 31), Fraction(11, 17)]
REPLICAS = 400


def main():
    result = {}
    for r in GRID:
        key = str(r)
        result[key] = {}
        for L in (8, 12):
            seed_key = f"prg-refine2-v1/L={L}/r={key}"
            seed = int.from_bytes(hashlib.sha256(seed_key.encode()).digest()[:8], "little")
            path = RAW / f"sw_refine2_L{L}_r{r.numerator}_{r.denominator}.jsonl"
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
        "experiment_id": "prg-sw-refine2-v1",
        "trigger": "Exact 200-replica pilots at r=13/20 show low L=12 m2 and prohibitively wide conservative Binder intervals.",
        "question": "Can a nearer positive-sign endpoint improve exact-sample statistical efficiency?",
        "status": "scouting_only_not_certified",
        "grid": [str(r) for r in GRID],
        "results": result,
    }
    OUT.write_text(json.dumps(payload, indent=2) + "\n")


if __name__ == "__main__":
    main()
