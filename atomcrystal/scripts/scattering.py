#!/usr/bin/env python3
"""Untrusted exact-rational candidate generator for the primitive driven slab.

Uses local Maxwell incidence and ionic Newton elimination, never continuum
theory or the existing eigenmode certificate. Lean rechecks every original
field/ion equation. --check compares regenerated artifacts without writing.
"""
import argparse
import hashlib
import json
from fractions import Fraction as F
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def solve(s, source=15, raw=False):
    # Schur elimination of (2-s)u=E and D=E+3*filling*u.
    ionic = F(2) - s
    mat = 1 + 3 / ionic
    face = 1 + F(3, 2) / ionic
    A = [[F(0) for _ in range(32)] for _ in range(32)]
    # Each electric face contributes c c^T/(1+3*filling/(2-s)).
    for side, epsilon in [(0, F(1)), (16, mat)]:
        for j in range(15):
            i, k = side+j, side+j+1
            for r, cr in [(i, -8), (k, 8)]:
                for c, cc in [(i, -8), (k, 8)]:
                    A[r][c] += F(cr*cc) / epsilon
        for j in range(16):
            A[side+j][side+j] += 6 / epsilon - s
    for r, cr in [(15, 8), (31, -8)]:
        for c, cc in [(15, 8), (31, -8)]:
            A[r][c] += F(cr*cc) / face
    rhs = [F(int(i == source)) for i in range(32)]
    # Exact Gaussian elimination; solver itself is outside the trust boundary.
    aug = [row[:] + [b] for row, b in zip(A, rhs)]
    for col in range(32):
        pivot = next(i for i in range(col, 32) if aug[i][col])
        aug[col], aug[pivot] = aug[pivot], aug[col]
        scale = aug[col][col]
        aug[col] = [x/scale for x in aug[col]]
        for i in range(col+1, 32):
            scale = aug[i][col]
            aug[i] = [x-scale*y for x, y in zip(aug[i], aug[col])]
    h = [F(0)]*32
    for i in reversed(range(32)):
        h[i] = aug[i][-1]-sum(aug[i][j]*h[j] for j in range(i+1, 32))
    assert all(sum(a*x for a, x in zip(row, h)) == b for row, b in zip(A, rhs))
    if raw:
        return A, h
    v, m = h[:16], h[16:]
    ve = [8*(v[j+1]-v[j]) for j in range(15)]
    me = [8*(m[j+1]-m[j])/mat for j in range(15)]
    ne = [x/mat for x in m]
    ie = 8*(v[15]-m[15])/face
    return dict(vacuumH=v, materialH=m, vacuumE=ve, materialE=me, normalE=ne,
                tangentialIon=[x/ionic for x in me], normalIon=[x/ionic for x in ne],
                interfaceE=ie, interfaceIon=ie/ionic)


def literal(x):
    return f"({x.numerator} / {x.denominator} : ℝ)"


def lean_field(name, values):
    lines = []
    for key, xs in values.items():
        if isinstance(xs, list):
            lines += [f"noncomputable def {name}_{key} : ℕ → ℝ", *[
                f"  | {i} => {literal(x)}" for i, x in enumerate(xs)], "  | _ => 0", ""]
    lines += [f"noncomputable def {name} : Fields where"]
    for key, xs in values.items():
        lines += [f"  {key} := " + (f"{name}_{key}" if isinstance(xs, list) else literal(xs))]
    return "\n".join(lines)


def unique_observable(name, s):
    A, dual_v = solve(s, 15, raw=True)
    _, dual_m = solve(s, 31, raw=True)
    inv_mat = 1 / (1 + 3/(2-s))
    inv_face = 1 / (1 + F(3, 2)/(2-s))
    lines = [f"theorem {name}_interface_unique (f : Fields) (hf : DrivenResponse 2 {s} 1 f) :",
             f"    f.vacuumH 15 = {name}.vacuumH 15 ∧ f.materialH 15 = {name}.materialH 15 := by",
             "  obtain ⟨hn, ht, hi, hui, hv0, hm0, hin, hv15, hm15⟩ := hf",
             f"  have ne (j : ℕ) (hj : j < 16) : f.normalE j = {literal(inv_mat)} * f.materialH j := by",
             "    obtain ⟨h1, h2⟩ := hn j hj", "    norm_num at h2", "    linarith",
             "  have ve (j : ℕ) (hj : j < 15) : f.vacuumE j = 8*(f.vacuumH (j+1)-f.vacuumH j) := (ht j hj).1",
             f"  have me (j : ℕ) (hj : j < 15) : f.materialE j = {literal(8*inv_mat)} * (f.materialH (j+1)-f.materialH j) := by",
             "    obtain ⟨_, h1, h2⟩ := ht j hj", "    norm_num at h2", "    linarith",
             f"  have ie : f.interfaceE = {literal(8*inv_face)} * (f.vacuumH 15-f.materialH 15) := by",
             "    norm_num at hui", "    linarith"]
    for i, row in enumerate(A):
        expr = " + ".join(f"{literal(c)} * f.{'vacuumH' if j < 16 else 'materialH'} {j%16}" for j, c in enumerate(row) if c)
        lines += [f"  have row{i} : {expr} = {int(i==15)} := by"]
        if i == 0:
            lines += ["    rw [ve 0 (by norm_num)] at hv0", "    norm_num at hv0", "    linarith"]
        elif i == 16:
            lines += ["    rw [me 0 (by norm_num), ne 0 (by norm_num)] at hm0", "    norm_num at hm0", "    linarith"]
        elif i == 15:
            lines += ["    rw [ve 14 (by norm_num), ie] at hv15", "    norm_num at hv15", "    linarith"]
        elif i == 31:
            lines += ["    rw [me 14 (by norm_num), ie, ne 15 (by norm_num)] at hm15", "    norm_num at hm15", "    linarith"]
        else:
            j = i%16-1
            field = "ve" if i < 16 else "me"
            lines += [f"    have h := (hin {j} (by norm_num)).{'1' if i < 16 else '2'}",
                      f"    rw [{field} {j} (by norm_num), {field} {j+1} (by norm_num)" +
                      (f", ne {j+1} (by norm_num)" if i >= 16 else "") + "] at h",
                      "    norm_num at h", "    linarith"]
    lines += ["  constructor"]
    for side, dual in [("vacuumH", dual_v), ("materialH", dual_m)]:
        lines += [f"  · norm_num only [{name}, {name}_{side}]",
                  "    linear_combination " + " + ".join(f"{literal(c)} * row{i}" for i, c in enumerate(dual) if c)]
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    frozen = ROOT / "artifacts/scattering_provenance/prediction.json"
    assert frozen.exists(), "Freeze before generating any candidate"
    data = json.loads(frozen.read_text())
    for name, digest in data["sha256"].items():
        assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == digest, name
    cases = [("resonant", F(3)), ("control", F(4))]
    results = {name: solve(s) for name, s in cases}
    artifact = {"prediction_snapshot_sha256": hashlib.sha256(frozen.read_bytes()).hexdigest(),
                "method": "exact rational Gaussian elimination of finite primitive Maxwell-ion equations",
                "results": {}}
    lean = ["import VerifiedPhysics.Experiments.AtomisticMaxwellScattering", "",
            "set_option maxRecDepth 100000", "set_option maxHeartbeats 8000000", "",
            "namespace VerifiedPhysics.GratingExperiment", "open MaxwellSlab", ""]
    for name, s in cases:
        f = results[name]
        intensity = f["vacuumH"][15]**2 + f["materialH"][15]**2
        far = sum(f["vacuumH"][j]**2+f["materialH"][j]**2 for j in range(8))
        total = sum(f["vacuumH"][j]**2+f["materialH"][j]**2 for j in range(16))
        artifact["results"][name] = {"s": str(s), "fields": {k: [str(x) for x in v] if isinstance(v, list) else str(v) for k, v in f.items()},
            "interface_intensity_exact": str(intensity), "interface_intensity_approx": float(intensity),
            "near_interface_fraction_approx": float(1-far/total)}
        lean += [lean_field(name, f), ""]
        defs = ", ".join([name] + [f"{name}_{k}" for k, v in f.items() if isinstance(v, list)])
        lean += [f"theorem {name}_equations : DrivenResponse 2 {s} 1 {name} := by",
                 "  unfold DrivenResponse", "  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩",
                 f"  · intro j hj; interval_cases j <;> norm_num [{defs}]",
                 f"  · intro j hj; interval_cases j <;> norm_num [{defs}]",
                 f"  · norm_num [{defs}]", f"  · norm_num [{defs}]",
                 f"  · norm_num [{defs}]", f"  · norm_num [{defs}]",
                 f"  · intro j hj; interval_cases j <;> norm_num [{defs}]",
                 f"  · norm_num [{defs}]", f"  · norm_num [{defs}]", ""]
        if name == "resonant":
            lean += ["theorem resonant_intensity : 1 ≤ interfaceIntensity resonant := by",
                     f"  norm_num [interfaceIntensity, {defs}]", "",
                     "theorem resonant_localization : farMagneticIntensity resonant ≤",
                     "    (2/5 : ℝ) * totalMagneticIntensity resonant := by",
                     f"  norm_num [farMagneticIntensity, totalMagneticIntensity, Finset.sum_range_succ, {defs}]", "",
                     "theorem resonant_ionic_participation : resonant.normalIon 15 ≠ 0 := by",
                     f"  norm_num [{defs}]", ""]
        else:
            lean += ["theorem control_intensity : interfaceIntensity control ≤ (1/4 : ℝ) := by",
                     f"  norm_num [interfaceIntensity, {defs}]", ""]
        lean += [unique_observable(name, s), ""]
    lean += ["end VerifiedPhysics.GratingExperiment", ""]
    outputs = {ROOT / "artifacts/scattering_certificate.json": json.dumps(artifact, indent=2)+"\n",
               ROOT / "VerifiedPhysics/Experiments/ScatteringCertificate.lean": "\n".join(lean)}
    for path, content in outputs.items():
        if args.check:
            assert path.read_text() == content, f"Not reproducible: {path}"
        else:
            path.write_text(content)
    print(json.dumps({k: {key: v for key, v in val.items() if key not in ("fields", "interface_intensity_exact")}
                      for k, val in artifact["results"].items()}, indent=2))


if __name__ == "__main__":
    main()
