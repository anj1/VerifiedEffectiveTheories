#!/usr/bin/env python3
"""Emit a Lean replay of the DFPT shell predictor from the primitive export."""
import argparse
from fractions import Fraction as Q
import json
from pathlib import Path

from dfpt_certificate import (
    case_inputs_source, contrast_definition, energy_source, parameters_source, sector_table,
)
from dfpt_shell_eft import ShellTrace, canonical, combine, load, manifest, predicted_sector
from fermion import sector
from pairing import lean_rat, lean_vec


def rat_argument(value):
    text = lean_rat(value)
    return f"({text})" if value > 0 and Q(value).denominator != 1 else text


def matrix_source(matrix):
    return lean_vec(lean_vec(map(lean_rat, row)) for row in matrix)


def block_source(index, block, states, n):
    kept = lean_vec(str(states[i]) for i in block.kept)
    discarded = lean_vec(str(states[i]) for i in block.discarded)
    coupling = [[row[j] for row in block.b] for j in range(len(block.discarded))]
    return f"""private def component{index} : ShellBlock {n} where
  p := {len(block.kept)}
  q := {len(block.discarded)}
  kept := {kept}
  discarded := {discarded}
  A := {matrix_source(block.a)}
  B := {matrix_source(coupling)}
  D := {matrix_source(block.d)}

"""


def replay_source(trace, states, electrons, n):
    lo, hi = map(rat_argument, trace.initial)
    components = "".join(block_source(i, block, states, n) for i, block in enumerate(trace.blocks))
    blocks = lean_vec(f"component{i}" for i in range(len(trace.blocks)))
    part = "".join(
        f"  | {' | '.join(str(states[i]) for i in block.kept + block.discarded)} => some {j}\n"
        for j, block in enumerate(trace.blocks)
    )
    chunks = 2**(2*n)//64
    rows = (f"  apply all_rows_of_chunks (chunks := {chunks}) rfl\n  intro i\n"
            "  fin_cases i <;> decide +kernel") if chunks else "  decide +kernel"
    pieces = [f"""{components}private def blocks : Fin {len(trace.blocks)} → ShellBlock {n} := {blocks}

private def part (j : State {n}) : Option (Fin {len(trace.blocks)}) :=
  match j.val with
{part}  | _ => none

private theorem setup : ShellSetup input modes {electrons} blocks part {lo} {hi} := by
  refine ⟨input_valid, modes_valid, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  apply shellRows_of_fast input input_valid
{rows}

theorem retained : ∀ k, (blocks k).retainedCheck input {electrons} activeOrbitals := by
  decide +kernel

private theorem step0 : SectorBracket input {electrons} {lo} {hi} :=
  ⟨setup.initialLower, electronic_trial input modes modes_valid {electrons} {hi}
    [({states[trace.initial_trial]}, 1)] (by decide +kernel)⟩

"""]
    final_trial = f"[({states[trace.initial_trial]}, 1)]"
    for i, step in enumerate(trace.steps, 1):
        z = rat_argument(step.trial_energy)
        by_block = {item.block: item for item in step.reductions}
        for item in step.reductions:
            pieces.append(f"""private def lift{i}_{item.block} : Fin (blocks {item.block}).q → Fin (blocks {item.block}).p → ℚ :=
  {matrix_source(item.weights)}

private theorem residual{i}_{item.block} :
    (blocks {item.block}).reductionCheck {z} ({lean_rat(item.delta)}) ({lean_rat(item.error)}) lift{i}_{item.block} := by
  decide +kernel

""")
        if step.update != "upper":
            e = rat_argument(step.trial_energy - (step.error if step.update == "intersect" else 0))
            proof = []
            for k in range(len(trace.blocks)):
                item = by_block.get(k)
                if item is None:
                    proof.append(f"  · exact setup.blockRowLower {k} {e} (by decide +kernel)")
                else:
                    factor = item.corrected if step.update == "lower" else item.positive
                    lower, diagonal = factor
                    # For an intersection step the zero-shift factor suffices:
                    # compare ε with the largest error before applying the bound.
                    residual_error = step.error if step.update == "intersect" else item.error
                    residual_proof = f"residual{i}_{k}"
                    if residual_error != item.error:
                        residual_proof = f"(ShellBlock.reductionCheck_mono residual{i}_{k} (by decide +kernel))"
                    eps = lean_rat(residual_error)
                    pieces.append(f"""private def factor{i}_{k} : Fin (blocks {k}).p → Fin (blocks {k}).p → ℚ :=
  {matrix_source(lower)}

private def pivots{i}_{k} : Fin (blocks {k}).p → ℚ := {lean_vec(map(lean_rat, diagonal))}

private theorem factorCheck{i}_{k} :
    (blocks {k}).gramCheck {z} (({eps}) - ({z} - {e})) lift{i}_{k} factor{i}_{k} pivots{i}_{k} := by
  decide +kernel

""")
                    proof.append(
                        f"  · exact setup.blockStepLower {k} {z} {e} ({lean_rat(item.delta)}) "
                        f"({eps}) lift{i}_{k} factor{i}_{k} pivots{i}_{k}\n"
                        f"      (by decide +kernel) {residual_proof} factorCheck{i}_{k}")
            pieces.append(f"""private theorem lower{i} :
    ∀ x, supported {electrons} x → (({e} : ℚ) : ℝ) * Grain.normSq x ≤ Grain.form (instantaneous input) x := by
  apply setup.lower (by decide +kernel)
  intro k
  fin_cases k
{chr(10).join(proof)}

""")
        if step.update != "lower":
            item = next(item for item in step.reductions if item.trial is not None and
                        (step.update == "intersect" or item.positive is None))
            k = item.block
            endpoint = step.trial_energy + (step.error if step.update == "intersect" else 0)
            e = rat_argument(endpoint)
            pieces.append(f"""private def trial{i} : Fin (blocks {k}).p → ℚ := {lean_vec(map(lean_rat, item.trial))}

private theorem upper{i} : SectorUpper input {electrons} {e} :=
  setup.blockStepUpper {k} {z} {e} ({lean_rat(item.delta)}) ({lean_rat(item.error)}) lift{i}_{k}
    trial{i} (by decide +kernel) residual{i}_{k} (by decide +kernel)

""")
            if endpoint == step.endpoints[1]:
                final_trial = f"(blocks {k}).trialVector lift{i}_{k} trial{i}"
        old_lo, old_hi = lo, hi
        lo, hi = map(rat_argument, step.endpoints)
        if step.update == "intersect":
            error = rat_argument(step.error)
            lower = rat_argument(step.trial_energy - step.error)
            upper = rat_argument(step.trial_energy + step.error)
            certificate = f"""  by
    have hlo : ({z} - {error} : ℚ) = {lower} := by decide +kernel
    have hhi : ({z} + {error} : ℚ) = {upper} := by decide +kernel
    have update := step{i-1}.intersect {z} {error} (by decide +kernel)
      (by simpa only [hlo] using lower{i}) (by simpa only [hhi] using upper{i})
    have hmax : max ({old_lo} : ℚ) ({z} - {error}) = {lo} := by decide +kernel
    have hmin : min ({old_hi} : ℚ) ({z} + {error}) = {hi} := by decide +kernel
    simpa only [hmax, hmin] using update
"""
        else:
            method = "updateUpper" if step.update == "upper" else "updateLower"
            certificate = f"  step{i-1}.{method} (by decide +kernel) {step.update}{i}\n"
        pieces.append(f"""private theorem step{i} : SectorBracket input {electrons} {lo} {hi} :=
{certificate}
""")
    return "".join(pieces), final_trial


def sector_source(case, electrons, active, tolerance, frozen):
    trace = ShellTrace()
    bounds = predicted_sector(case, electrons, active, tolerance, trace, diagnostics=False)
    if any(frozen[key] != value for key, value in canonical(bounds).items()):
        raise ValueError(f"frozen prediction did not reproduce in N={electrons}")
    n = len(case.levels)
    replay, trial = replay_source(trace, sector(n, electrons), electrons, n)
    lo, hi = map(lean_rat, bounds["instantaneous"])
    parent_hi = lean_rat(bounds["parent"][1] - case.upstream)
    return f"""namespace Shell{electrons}

{replay}def lower : ℚ := {lo}
def upper : ℚ := {hi}
def harmonicUpper : ℚ := {parent_hi}

theorem bracket : SectorBracket input {electrons} lower upper :=
  step{len(trace.steps)}

theorem resolution : upper - lower ≤ energyResolution := by decide +kernel

theorem electronic :
    (lower : ℝ) ≤ electronicGround input {electrons} ∧ electronicGround input {electrons} ≤ (upper : ℝ) :=
  bracket.bounds

private def dressedTrial : SectorWitness {n} where
  lower := lower
  electronicUpper := upper
  trialUpper := upper
  harmonicUpper := harmonicUpper
  weights := fun _ => 1
  trial := {trial}

theorem harmonic :
    ((lower - upstreamSectorError : ℚ) : ℝ) ≤ harmonicGround input {electrons} ∧
      harmonicGround input {electrons} ≤ ((harmonicUpper + upstreamSectorError : ℚ) : ℝ) :=
  widen_bounds (by decide +kernel) (harmonic_trial_certificate input input_valid modes modes_valid
    omega omega_valid {electrons} dressedTrial bracket.lower (by decide +kernel))

end Shell{electrons}

"""


def contrast_source(label, ground, count, electrons, interval):
    def endpoint(i, k, upper):
        case = f"Case{i}"
        shell = f"{case}.Shell{k}"
        if label == "electronic":
            return f"{shell}.{'upper' if upper else 'lower'}"
        name, sign = ("harmonicUpper", "+") if upper else ("lower", "-")
        return f"({shell}.{name} {sign} {case}.upstreamSectorError)"

    lows = sector_table(count, electrons, lambda i, k: endpoint(i, k, False))
    highs = sector_table(count, electrons, lambda i, k: endpoint(i, k, True))
    proofs = ", ".join(f"Case{i}.Shell{k}.{label}" for i in range(count) for k in electrons)
    lo, hi = map(Q, interval)
    return f"""{energy_source(label, ground, count, electrons)}private def {label}PredictionLo (a : Index) : ℚ := ({lows} a.1) a.2
private def {label}PredictionHi (a : Index) : ℚ := ({highs} a.1) a.2

private theorem {label}PredictionSectors (a : Index) :
    ({label}PredictionLo a : ℝ) ≤ {label}Energy a ∧ {label}Energy a ≤ ({label}PredictionHi a : ℝ) := by
  obtain ⟨i, j⟩ := a
  fin_cases i <;> fin_cases j
  exacts [{proofs}]

{contrast_definition(label)}theorem {label}_prediction :
    (({lean_rat(lo)} : ℚ) : ℝ) ≤ {label}Contrast ∧ {label}Contrast ≤ (({lean_rat(hi)} : ℚ) : ℝ) :=
  certified_contrast weight {label}PredictionLo {label}PredictionHi {label}Energy {label}PredictionSectors
    ({lean_rat(lo)}) ({lean_rat(hi)}) (by decide +kernel) (by decide +kernel)

"""


def lean_source(path, frozen, namespace):
    cases, odd, active, weights, tolerance = load(path)
    raw = json.loads(path.read_text(), parse_float=Q)
    if frozen["manifest"] != manifest(path):
        raise ValueError("frozen input or prediction code changed")
    prediction = frozen["prediction"]
    electrons = (odd - 1, odd, odd + 1)
    pieces = [f"""import Grain.DFPTShell

/- Generated by scripts/dfpt_shell_certificate.py from the export and the predictor trace. -/

namespace Grain.HarmonicBand.{namespace}

open scoped BigOperators

set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option Elab.async false

""", parameters_source(cases, odd, active, weights, tolerance)]
    for i, (name, case) in enumerate(cases.items()):
        pieces += [f"namespace Case{i}\n\n", case_inputs_source(raw["cases"][name], case)]
        for k in electrons:
            pieces.append(sector_source(case, k, active, tolerance, prediction["sectors"][name][str(k)]))
        pieces.append(f"end Case{i}\n\n")
    for label, quantity, ground in (("electronic", "instantaneous", "electronicGround"),
                                   ("harmonic", "parent", "harmonicGround")):
        interval = prediction[f"{quantity}_contrast_mev"]
        expected = combine(
            (weight * (1 if k == odd else Q(-1, 2)),
             tuple(map(Q, prediction["sectors"][name][str(k)][quantity])))
            for name, weight in weights.items() for k in electrons
        )
        if tuple(map(Q, interval)) != expected:
            raise ValueError(f"frozen {quantity} contrast did not reproduce")
        pieces.append(contrast_source(label, ground, len(cases), electrons, interval))
    return "".join(pieces) + f"end Grain.HarmonicBand.{namespace}\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path)
    parser.add_argument("prediction", type=Path)
    parser.add_argument("--namespace", default="DFPTFive")
    args = parser.parse_args()
    if not args.namespace.isidentifier():
        parser.error("namespace must be a Lean identifier")
    try:
        print(lean_source(args.input, json.loads(args.prediction.read_text()), args.namespace), end="")
    except (ArithmeticError, KeyError, TypeError, ValueError, OSError) as error:
        parser.error(str(error))


if __name__ == "__main__":
    main()
