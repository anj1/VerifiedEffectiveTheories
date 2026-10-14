"""Independent replay diagnostics for version-4 CFTP samples.

This validates selected deterministic streams against the recorded state
observables. It cannot turn SplitMix64 into a theorem of random independence.
"""
import hashlib
import json
import math
from pathlib import Path

ROOT = Path(__file__).resolve().parent
RAW = ROOT / "grandcanonical_data" / "prg_raw"
OUT = ROOT / "grandcanonical_results" / "prg_validation.json"
MASK = (1 << 64) - 1


class SplitMix:
    def __init__(self, state):
        self.state = state

    def word(self):
        self.state = (self.state + 0x9e3779b97f4a7c15) & MASK
        z = self.state
        z = ((z ^ (z >> 30)) * 0xbf58476d1ce4e5b9) & MASK
        z = ((z ^ (z >> 27)) * 0x94d049bb133111eb) & MASK
        return z ^ (z >> 31)

    def below(self, n):
        threshold = ((1 << 64) - n) % n
        while True:
            x = self.word()
            if x >= threshold:
                return x % n


def neighbour(L, site):
    x = site % L
    y = site // L % L
    z = site // (L * L)
    index = lambda i, j, k: i + L * (j + L * k)
    return (index((x + 1) % L, y, z), index((x - 1) % L, y, z),
            index(x, (y + 1) % L, z), index(x, (y - 1) % L, z),
            index(x, y, (z + 1) % L), index(x, y, (z - 1) % L))


def replay(row):
    L = row["L"]
    V = L ** 3
    n, d = row["r_num"], row["r_den"]
    M = row["rational_uniform_denominator"]
    rng = SplitMix(row["seed"])
    blocks = []
    old = 0
    target = 1
    while target <= row["horizon_updates"]:
        blocks.append([(rng.below(V), rng.below(M)) for _ in range(old, target)])
        old = target
        target *= 2
    assert old == row["horizon_updates"]
    neighbours = [neighbour(L, x) for x in range(V)]
    lo, hi = [0] * V, [1] * V
    p = []
    for a in range(7):
        numerator = n ** (6 - a) * d ** a
        denominator = numerator + n ** a * d ** (6 - a)
        p.append((numerator, denominator))
    for block in reversed(blocks):
        for site, u in block:
            for spin in (lo, hi):
                a = sum(spin[v] for v in neighbours[site])
                num, den = p[a]
                spin[site] = int(u * den < M * num)
    assert lo == hi and row["success"]
    state = lo
    h = 14695981039346656037
    for bit in state:
        h = ((h ^ bit) * 1099511628211) & MASK
    m = sum(2 * bit - 1 for bit in state)
    D = sum(state[x] != state[neighbours[x][j]] for x in range(V) for j in (0, 2, 4))
    planes = [[0] * L for _ in range(3)]
    for site, bit in enumerate(state):
        x, y, z = site % L, site // L % L, site // (L * L)
        for axis, coordinate in enumerate((x, y, z)):
            planes[axis][coordinate] += 2 * bit - 1
    assert h == row["state_fnv64"]
    assert m == row["magnetization_sum"]
    assert m ** 2 == row["magnetization_sum_2"]
    assert m ** 4 == row["magnetization_sum_4"]
    assert D == row["disagreement_count"]
    assert planes == row["plane_spin_sums"]
    return {"L": L, "r": f"{n}/{d}", "replica": row["replica"],
            "horizon": row["horizon_updates"], "state_fnv64": h,
            "D": D, "magnetization_sum": m}


def main():
    selected = [(4, 16, 25, 2000), (6, 16, 25, 2000),
                (8, 16, 25, 1000), (12, 13, 20, 1000)]
    checks = []
    artifacts = {}
    for L, a, b, n in selected:
        path = RAW / f"cftp_prg_L{L}_r{a}_{b}_n{n}.jsonl"
        with path.open() as file:
            row = json.loads(next(file))
        checks.append(replay(row))
        artifacts[str(path.relative_to(ROOT))] = hashlib.sha256(path.read_bytes()).hexdigest()
        print(f"replayed L={L} r={a}/{b} horizon={row['horizon_updates']}", flush=True)
    for L, a, b in ((8, 7, 11), (12, 7, 11), (8, 20, 31), (12, 20, 31)):
        path = RAW / f"cftp_covhold_L{L}_r{a}_{b}_n5000.jsonl"
        with path.open() as file:
            row = json.loads(next(file))
        checks.append(replay(row))
        artifacts[str(path.relative_to(ROOT))] = hashlib.sha256(path.read_bytes()).hexdigest()
        print(f"replayed holdout L={L} r={a}/{b} horizon={row['horizon_updates']}", flush=True)
    for L in (8, 12):
        path = RAW / f"cftp_covstage2_L{L}_r20_31_n30000.jsonl"
        with path.open() as file:
            row = json.loads(next(file))
        checks.append(replay(row))
        artifacts[str(path.relative_to(ROOT))] = hashlib.sha256(path.read_bytes()).hexdigest()
        print(f"replayed stage2 L={L} r=20/31 horizon={row['horizon_updates']}", flush=True)
    result = {"status": "deterministic_replay_verified_selected_streams",
              "checks": checks, "raw_sha256": artifacts,
              "limitation": "Selected replay checks are not a universal C++-Lean compiler-correctness proof and do not establish PRNG independence."}
    OUT.write_text(json.dumps(result, indent=2) + "\n")


if __name__ == "__main__":
    main()
