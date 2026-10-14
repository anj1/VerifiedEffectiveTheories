"""CFTP feasibility and effect-size pilots requested by the SW scout.

These observations select confirmatory endpoints and sample counts; they must
not be pooled into a later confidence or quotient interval.
"""
import hashlib
import json
import math
import subprocess
from concurrent.futures import ThreadPoolExecutor
from fractions import Fraction as F
from pathlib import Path

ROOT = Path(__file__).resolve().parent
RAW = ROOT / "grandcanonical_data" / "prg_raw"
OUT = ROOT / "grandcanonical_results" / "prg_stage4_pilot.json"
EXE = ROOT / "build" / "grandcanonical_prg_v4"
N = 1000


def seed(L, r):
    key = f"stage4-CFTP-pilot/L{L}/r{r}"
    return int.from_bytes(hashlib.sha256(key.encode()).digest()[:8], "little")


def run_cell(cell):
    L, r = cell
    path = RAW / f"cftp_stage4_pilot_L{L}_r{r.numerator}_{r.denominator}_n{N}.jsonl"
    if not path.exists():
        subprocess.run([str(EXE), "cftp", str(L), str(r.numerator),
                        str(r.denominator), str(N), str(seed(L, r)),
                        str(1 << 26), "0", str(path)], check=True)
    rows = [json.loads(line) for line in path.read_text().splitlines()]
    assert len(rows) == N and len({z["seed"] for z in rows}) == N
    coalesced = [z for z in rows if z["success"]]
    result = {"L": L, "r": str(r), "requested": N,
              "coalesced": len(coalesced), "raw_file": str(path.relative_to(ROOT)),
              "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
              "max_horizon_updates": max(z["horizon_updates"] for z in rows)}
    if len(coalesced) == N:
        V = L ** 3
        x = [z["magnetization_sum_2"] / V ** 2 for z in rows]
        y = [z["magnetization_sum_4"] / V ** 4 for z in rows]
        a = sum(x) / N
        b = sum(y) / N
        result.update({"m2": a, "m4": b, "R": b / a ** 2,
                       "U4": 1 - b / (3 * a ** 2),
                       "mean_D": sum(z["disagreement_count"] for z in rows) / N})
        ia, ib = 2 * b / (3 * a ** 3), -1 / (3 * a ** 2)
        infl = [ia * (xx - a) + ib * (yy - b) for xx, yy in zip(x, y)]
        result["delta_method_se_design_only"] = math.sqrt(
            sum(v * v for v in infl) / ((N - 1) * N))
    return result


def main():
    scout = json.loads((ROOT / "grandcanonical_results/prg_stage4_scout.json").read_text())
    cells = set()
    requests = {}
    for pair, data in scout["pairs"].items():
        sizes = (4, 6) if pair == "4_to_6" else (8, 12)
        chosen = [F(x) for x in data["decision"]["CFTP_request"]]
        requests[pair] = list(map(str, chosen))
        for r in chosen:
            for L in sizes:
                cells.add((L, r))
        if pair == "8_to_12":
            positives = [F(key) for key, p in data["results"].items()
                         if p["delta_U4"] > 0]
            strongest = max(positives, key=lambda r:
                data["results"][str(r)]["delta_U4"] /
                data["results"][str(r)]["delta_se_design_only"])
            if strongest != chosen[1]:
                requests[pair].append(str(strongest))
                for L in sizes:
                    cells.add((L, strongest))
    with ThreadPoolExecutor(max_workers=4) as pool:
        results = list(pool.map(run_cell, sorted(cells)))
    points = {f'L{z["L"]}_r{z["r"]}': z for z in results}
    deltas = {}
    for pair, rs in requests.items():
        a, b = (4, 6) if pair == "4_to_6" else (8, 12)
        for r in rs:
            x, y = points[f"L{a}_r{r}"], points[f"L{b}_r{r}"]
            if "U4" in x and "U4" in y:
                deltas[f"{pair}_r{r}"] = {
                    "point": x["U4"] - y["U4"],
                    "design_se": math.hypot(x["delta_method_se_design_only"],
                                             y["delta_method_se_design_only"])}
    payload = {"status": "CFTP_pilot_design_only", "n_per_cell": N,
               "question": "Which narrowed endpoint signs are feasible to certify with fresh CFTP holdouts?",
               "requests": requests, "points": points, "delta_U4": deltas,
               "decision_pending": "Choose fresh confirmatory endpoints and counts from these pilots; never pool them into confidence bounds."}
    OUT.write_text(json.dumps(payload, indent=2) + "\n")
    for key, p in deltas.items():
        print(key, f'delta={p["point"]:+.5f}',
              f'design_se={p["design_se"]:.5f}', flush=True)


if __name__ == "__main__":
    main()
