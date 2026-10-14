"""Fresh Swendsen--Wang scouting for the L=8,12 phenomenological-RG pair.

This is a design instrument only. It must never enter a CFTP confidence bound.
The grid is broad and does not contain an externally supplied critical parameter.
"""
import hashlib
import json
import math
import subprocess
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parent
RAW = ROOT / "grandcanonical_data" / "prg_raw"
OUT = ROOT / "grandcanonical_results" / "prg_scout.json"
EXE = ROOT / "build" / "grandcanonical_prg"
GRID = [Fraction(3, 5), Fraction(5, 8), Fraction(16, 25),
        Fraction(13, 20), Fraction(2, 3), Fraction(7, 10)]
SIZES = [8, 12]
REPLICAS = 400


def seed_for(L, r):
    key = f"prg-scout-v1/L={L}/r={r.numerator}/{r.denominator}"
    return int.from_bytes(hashlib.sha256(key.encode()).digest()[:8], "little")


def estimate(path):
    rows = [json.loads(line) for line in path.read_text().splitlines()]
    assert len(rows) == REPLICAS
    assert all(row["model_version"] in ("grandcanonical-v3-prg", "grandcanonical-v4-prg") for row in rows)
    L = rows[0]["L"]
    V = L ** 3
    x = [row["magnetization_sum_2"] / V ** 2 for row in rows]
    y = [row["magnetization_sum_4"] / V ** 4 for row in rows]
    a = sum(x) / len(x)
    b = sum(y) / len(y)
    u = 1 - b / (3 * a * a)
    da = 2 * b / (3 * a ** 3)
    db = -1 / (3 * a * a)
    influence = [da * (xx - a) + db * (yy - b) for xx, yy in zip(x, y)]
    se = math.sqrt(sum(v * v for v in influence) / ((len(x) - 1) * len(x)))
    return {"n": len(rows), "U4": u, "delta_method_se_scout_only": se,
            "mean_m2": a, "mean_m4": b,
            "mean_D": sum(row["disagreement_count"] for row in rows) / len(rows),
            "raw_file": str(path.relative_to(ROOT))}


def main():
    RAW.mkdir(parents=True, exist_ok=True)
    OUT.parent.mkdir(parents=True, exist_ok=True)
    results = {}
    for r in GRID:
        key = f"{r.numerator}/{r.denominator}"
        results[key] = {}
        for L in SIZES:
            path = RAW / f"sw_scout_L{L}_r{r.numerator}_{r.denominator}.jsonl"
            if not path.exists():
                subprocess.run([str(EXE), "sw", str(L), str(r.numerator),
                                str(r.denominator), str(REPLICAS), str(seed_for(L, r)),
                                "32", "8", str(path)], check=True)
            results[key][str(L)] = estimate(path)
        delta = results[key]["8"]["U4"] - results[key]["12"]["U4"]
        se = math.hypot(results[key]["8"]["delta_method_se_scout_only"],
                        results[key]["12"]["delta_method_se_scout_only"])
        results[key]["delta_U4_8_minus_12"] = delta
        results[key]["delta_se_scout_only"] = se
        print(f"r={key:>5}  delta={delta:+.6f}  scout_se={se:.6f}", flush=True)

    # Choose the strongest negative and positive signs under a broad width cap.
    # This rule is fixed before seeing this run's observations. It deliberately
    # selects endpoints rather than any externally known critical value.
    choices = []
    for ra in GRID:
        for rb in GRID:
            if not (ra < rb and rb - ra <= Fraction(1, 10)):
                continue
            ka, kb = str(ra), str(rb)
            da = results[ka]["delta_U4_8_minus_12"]
            db = results[kb]["delta_U4_8_minus_12"]
            if da < 0 < db:
                za = -da / results[ka]["delta_se_scout_only"]
                zb = db / results[kb]["delta_se_scout_only"]
                choices.append((min(za, zb), za + zb, ra, rb))
    choices.sort(reverse=True)
    choice = None
    if choices:
        _, _, ra, rb = choices[0]
        choice = {"r_negative": str(ra), "r_positive": str(rb),
                  "selection_rule": "maximize min endpoint scout z-score among opposite-sign pairs of width <= 1/10"}
    payload = {
        "experiment_id": "prg-sw-scout-v1",
        "model_version": "grandcanonical-v3-prg",
        "status": "scouting_only_not_certified",
        "question": "Does the Binder crossing persist under the scale transformation 8 to 12?",
        "proposed_experiment": "Independent-seed SW replicas on a broad rational grid; select fresh CFTP bracket from observed signs.",
        "initial_grid": [str(r) for r in GRID],
        "replicas_per_cell": REPLICAS,
        "sw_initial_sweeps": 32,
        "sw_extra_sweeps": 8,
        "uncertainty_warning": "Delta-method standard errors are design heuristics; SW equilibration and autocorrelation are not certified.",
        "results": results,
        "decision": choice or {"status": "no_opposite_sign_pair; expand scout"},
    }
    OUT.write_text(json.dumps(payload, indent=2) + "\n")
    print(json.dumps(payload["decision"], indent=2), flush=True)


if __name__ == "__main__":
    main()
