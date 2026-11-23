import Grain.ParityMatching
import Grain.ResolventRemainder
import Grain.ShellPrediction

namespace Grain.ParityMatching

open ResolventRemainder

noncomputable def inverseInner (far : Bool) : ℝ := if far then 1 / 5 else 1 / 2
noncomputable def inverseOuter (far : Bool) : ℝ := if far then 1 / 14 else 1 / 6

noncomputable def strength (r s : Bool) : ℝ :=
  let a := inverseInner r + inverseOuter s
  let q := inverseInner r ^ 2 + inverseOuter s ^ 2
  1 / 100 + (1 / 100)^2 * a + (1 / 100)^3 * (a^2 - q/2)

noncomputable def fullPolynomial (r s : Bool) : ℝ :=
  let a := inverseInner r + inverseOuter s
  let q := inverseInner r ^ 2 + inverseOuter s ^ 2
  1 / 200 + (1 / 100)^2 * (1+a)/2 + (1 / 100)^3 * ((1+a)^2/2 - (1+q)/4)

noncomputable def retainedPolynomial (r s : Bool) : ℝ :=
  let k := strength r s
  k/2 + k^2/2 + k^3/4

/-- Uniform evaluation of the sector budgets and matching error in spacing units. -/
theorem benchmark_budget (r s : Bool) :
    0 < strength r s ∧
    strength r s * 2 < 2 ∧
    budget 2 (1 / 100) 12 12 ≤ 252 / 10^8 ∧
    budget 2 (strength r s) 2 2 ≤ 16 / 10^9 ∧
    |retainedPolynomial r s - fullPolynomial r s| ≤ 11 / 10^9 := by
  cases r <;> cases s <;>
    norm_num [strength, inverseInner, inverseOuter, budget, retainedPolynomial, fullPolynomial, abs_le]

noncomputable def mixed (p : Bool → Bool → ℝ) : ℝ :=
  p false false - p false true - p true false + p true true

set_option maxHeartbeats 0 in
theorem full_benchmark_polynomial_error (r s : Bool) :
    |TwoShell.Prediction.parityEnergy r s - fullPolynomial r s| ≤
      2 * budget 2 (1 / 100) 12 12 := by
  have h₀ := abs_le.mp (TwoShell.Prediction.sector_error r s 0)
  have h₁ := abs_le.mp (TwoShell.Prediction.sector_error r s 1)
  have h₂ := abs_le.mp (TwoShell.Prediction.sector_error r s 2)
  rw [abs_le]
  cases r <;> cases s <;>
    norm_num [TwoShell.Prediction.parityEnergy,
      TwoShell.Prediction.center, TwoShell.Prediction.prediction,
      TwoShell.Prediction.r2s6n6Center, TwoShell.Prediction.r2s6n7Center, TwoShell.Prediction.r2s6n8Center,
      TwoShell.Prediction.r2s14n6Center, TwoShell.Prediction.r2s14n7Center, TwoShell.Prediction.r2s14n8Center,
      TwoShell.Prediction.r5s6n6Center, TwoShell.Prediction.r5s6n7Center, TwoShell.Prediction.r5s6n8Center,
      TwoShell.Prediction.r5s14n6Center, TwoShell.Prediction.r5s14n7Center, TwoShell.Prediction.r5s14n8Center,
      TwoShell.Prediction.sectorTolerance, fullPolynomial,
      inverseInner, inverseOuter, budget] at h₀ h₁ h₂ ⊢ <;>
    obtain ⟨_, _⟩ := h₀ <;> obtain ⟨_, _⟩ := h₁ <;> obtain ⟨_, _⟩ := h₂ <;>
    constructor <;> linarith

/-- Propagate the two models' sector-derived parity bounds through the mixed contrast. -/
theorem benchmark_scalar_error (full retained : Bool → Bool → ℝ)
    (hf : ∀ r s, |full r s - fullPolynomial r s| ≤ 2 * budget 2 (1 / 100) 12 12)
    (hr : ∀ r s, |retained r s - retainedPolynomial r s| ≤ 2 * budget 2 (strength r s) 2 2) :
    |mixed full - mixed retained| ≤ 204 / 10^7 := by
  have caseBound (r s : Bool) : |full r s - retained r s| ≤ 51 / 10^7 := by
    obtain ⟨_, _, hb, hk, hp⟩ := benchmark_budget r s
    have h₁ := abs_le.mp (hf r s)
    have h₂ := abs_le.mp (hr r s)
    have h₃ := abs_le.mp hp
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have h₁ := abs_le.mp (caseBound false false)
  have h₂ := abs_le.mp (caseBound false true)
  have h₃ := abs_le.mp (caseBound true false)
  have h₄ := abs_le.mp (caseBound true true)
  unfold mixed
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The full-model premise follows from the certified nested reduction. -/
theorem benchmark_scalar_error_of_retained (retained : Bool → Bool → ℝ)
    (hr : ∀ r s, |retained r s - retainedPolynomial r s| ≤
      2 * budget 2 (strength r s) 2 2) :
    |TwoShell.Prediction.mixedContrast - mixed retained| ≤ 204 / 10^7 :=
  benchmark_scalar_error TwoShell.Prediction.parityEnergy retained
    full_benchmark_polynomial_error hr

end Grain.ParityMatching
