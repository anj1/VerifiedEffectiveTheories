"""Adaptive, design-only scouting from the two previously certified brackets.

Mediants are generated from the bracket endpoints, not from a known critical
parameter. SW is only used to request fresh CFTP experiments, never to certify
an equilibrium sign or quotient.
"""
import hashlib
import json
import math
import subprocess
from fractions import Fraction as F
from pathlib import Path

ROOT = Path(__file__).resolve().parent
RAW = ROOT / "grandcanonical_data" / "prg_raw"
OUT = ROOT / "grandcanonical_results" / "prg_stage4_scout.json"
EXE = ROOT / "build" / "grandcanonical_prg_v4"
N = 1000


def med(a, b):
    return F(a.numerator + b.numerator, a.denominator + b.denominator)


def seed(pair, L, r):
    key = f"stage4-mediant-scout/{pair}/L{L}/r{r}"
    return int.from_bytes(hashlib.sha256(key.encode()).digest()[:8], "little")


def point(path, L):
    rows = [json.loads(line) for line in path.read_text().splitlines()]
    assert len(rows) == N and len({z["seed"] for z in rows}) == N
    assert all(z["model_version"] == "grandcanonical-v4-prg" and
               z["algorithm"] == "sw" and z["L"] == L for z in rows)
    V = L ** 3
    x = [z["magnetization_sum_2"] / V ** 2 for z in rows]
    y = [z["magnetization_sum_4"] / V ** 4 for z in rows]
    a = sum(x) / N
    b = sum(y) / N
    u = 1 - b / (3 * a * a)
    ia, ib = 2 * b / (3 * a ** 3), -1 / (3 * a * a)
    influence = [ia * (xx - a) + ib * (yy - b) for xx, yy in zip(x, y)]
    se = math.sqrt(sum(v * v for v in influence) / ((N - 1) * N))
    return {"U4": u, "delta_method_se_scout_only": se,
            "m2": a, "m4": b, "raw_file": str(path.relative_to(ROOT)),
            "raw_sha256": hashlib.sha256(path.read_bytes()).hexdigest()}


def main():
    brackets = {"4_to_6": (F(5, 8), F(2, 3)),
                "8_to_12": (F(7, 11), F(20, 31))}
    payload = {"status": "SW_design_only", "replicas_per_cell": N,
               "sw_sweeps": [32, 8], "known_critical_input": False,
               "question": "Where can each certified size-crossing bracket be narrowed with fresh exact samples?",
               "pairs": {}}
    for pair, (left, right) in brackets.items():
        sizes = (4, 6) if pair == "4_to_6" else (8, 12)
        middle = med(left, right)
        grid = sorted({med(left, middle), middle, med(middle, right)})
        results = {}
        for r in grid:
            p = {}
            for L in sizes:
                path = RAW / f"sw_stage4_L{L}_r{r.numerator}_{r.denominator}.jsonl"
                if not path.exists():
                    subprocess.run([str(EXE), "sw", str(L), str(r.numerator),
                                    str(r.denominator), str(N), str(seed(pair, L, r)),
                                    "32", "8", str(path)], check=True)
                p[str(L)] = point(path, L)
            p["delta_U4"] = p[str(sizes[0])]["U4"] - p[str(sizes[1])]["U4"]
            p["delta_se_design_only"] = math.hypot(
                p[str(sizes[0])]["delta_method_se_scout_only"],
                p[str(sizes[1])]["delta_method_se_scout_only"])
            results[str(r)] = p
            print(pair, str(r), f'delta={p["delta_U4"]:+.5f}',
                  f'scout_se={p["delta_se_design_only"]:.5f}', flush=True)
        signed = [r for r in grid if abs(results[str(r)]["delta_U4"]) >=
                  results[str(r)]["delta_se_design_only"]]
        candidates = [(hi - lo, lo, hi) for lo in signed for hi in signed
                      if lo < hi and results[str(lo)]["delta_U4"] < 0 <
                      results[str(hi)]["delta_U4"]]
        chosen = min(candidates) if candidates else None
        payload["pairs"][pair] = {"input_interval": [str(left), str(right)],
                                  "grid_rule": "three successive mediants of input interval",
                                  "grid": [str(r) for r in grid], "results": results,
                                  "decision": ({"CFTP_request": [str(chosen[1]), str(chosen[2])],
                                                "rule": "narrowest opposite-sign pair with each scout |delta| >= 1 design SE"}
                                               if chosen else
                                               {"CFTP_request": None,
                                                "rule": "expand scout; no pair passed 1-SE design threshold"})}
    OUT.write_text(json.dumps(payload, indent=2) + "\n")


if __name__ == "__main__":
    main()
