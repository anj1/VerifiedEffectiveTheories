import Grain.ScalarOccupation

/-! The scalar parity budget from the occupation Hamiltonians. -/

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

theorem strength_cast (r s : Bool) : (rationalStrength r s : ℝ) = strength r s := by
  cases r <;> cases s <;>
    norm_num [rationalStrength, cubicMatchedCoupling, strength, inverseInner, inverseOuter]

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

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem full_polynomial_value (r s : Bool) :
    (polynomialParity (fullSectorPolynomial r s) : ℝ) = fullPolynomial r s := by
  have h (r s : Bool) :
      polynomialParity (fullSectorPolynomial r s) =
        let a : ℚ := (if r then 1/5 else 1/2) + (if s then 1/14 else 1/6)
        let q : ℚ := (if r then 1/5 else 1/2)^2 + (if s then 1/14 else 1/6)^2
        1/200 + (1/100)^2 * (1+a)/2 + (1/100)^3 * ((1+a)^2/2 - (1+q)/4) := by
    cases r <;> cases s <;> decide +kernel
  rw [h]
  cases r <;> cases s <;> norm_num [fullPolynomial, inverseInner, inverseOuter]

private theorem retained_polynomial_value (r s : Bool) :
    (polynomialParity (retainedSectorPolynomial r s) : ℝ) = retainedPolynomial r s := by
  have h (r s : Bool) :
      polynomialParity (retainedSectorPolynomial r s) =
        let k := rationalStrength r s
        k/2 + k^2/2 + k^3/4 := by
    cases r <;> cases s <;> decide +kernel
  rw [h]
  push_cast
  rw [strength_cast]
  rfl

theorem full_benchmark_polynomial_error (r s : Bool) :
    |fullParity r s - fullPolynomial r s| ≤ 2 * budget 2 (1 / 100) 12 12 := by
  rw [← full_polynomial_value]
  simpa only [fullParity, polynomialParity, Rat.cast_sub, Rat.cast_add,
    Rat.cast_div, Rat.cast_ofNat] using
    parity_error (fullEnergy r s) (fun c => (fullSectorPolynomial r s c : ℝ))
      (full_sector_polynomial_error r s)

theorem retained_benchmark_polynomial_error (r s : Bool) :
    |retainedParity r s - retainedPolynomial r s| ≤ 2 * budget 2 (strength r s) 2 2 := by
  rw [← retained_polynomial_value, ← strength_cast]
  simpa only [retainedParity, polynomialParity, Rat.cast_sub, Rat.cast_add,
    Rat.cast_div, Rat.cast_ofNat] using
    parity_error (fun c => ground (retainedH r s c)) (fun c => (retainedSectorPolynomial r s c : ℝ))
      (retained_sector_polynomial_error r s)

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

theorem benchmark_scalar_error_of_retained (retained : Bool → Bool → ℝ)
    (hr : ∀ r s, |retained r s - retainedPolynomial r s| ≤
      2 * budget 2 (strength r s) 2 2) :
    |mixed fullParity - mixed retained| ≤ 204 / 10^7 :=
  benchmark_scalar_error fullParity retained full_benchmark_polynomial_error hr

theorem benchmark_analytic_error :
    |mixed fullParity - mixed retainedParity| ≤ 204 / 10^7 :=
  benchmark_scalar_error_of_retained retainedParity retained_benchmark_polynomial_error

end Grain.ParityMatching
