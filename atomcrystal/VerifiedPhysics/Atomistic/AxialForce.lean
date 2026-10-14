import VerifiedPhysics.Atomistic.NonlinearPotential

namespace VerifiedPhysics

noncomputable def axialNonlinearGradient (x : ℝ) : ℝ :=
  coulombMagnitude / (1 + x) ^ 2 -
    coulombMagnitude / (1 + x) ^ 3 +
    (6 - coulombMagnitude) * x

theorem axial_gradient_eq_deriv (x : ℝ) (hx : -1 < x) :
    deriv axialNonlinearPotential x = axialNonlinearGradient x := by
  have hne : 1 + x ≠ 0 := by linarith
  have hb : HasDerivAt (fun y : ℝ => 1 + y) 1 x := by
    convert (hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x) using 1
    · funext y; simp
    · norm_num
  have h1 : HasDerivAt (fun y : ℝ => 1 / (1 + y))
      (-(1 + x)⁻¹ ^ 2) x := by
    convert hb.inv hne using 1
    · funext y; simp [one_div]
    · field_simp [hne]
  have h2 : HasDerivAt (fun y : ℝ => 1 / (2 * (1 + y) ^ 2))
      (-(1 + x)⁻¹ ^ 3) x := by
    convert (h1.pow 2).const_mul (1 / 2 : ℝ) using 1
    · funext y; simp [one_div, inv_pow]; ring
    · dsimp; ring
  have h3 : HasDerivAt (fun y : ℝ => ((6 - coulombMagnitude) / 2) * y ^ 2)
      ((6 - coulombMagnitude) * x) x := by
    convert ((hasDerivAt_id x).pow 2).const_mul ((6 - coulombMagnitude) / 2) using 1
    · funext y; simp
    · simp; ring
  unfold axialNonlinearPotential axialNonlinearGradient
  rw [show (fun y : ℝ => -coulombMagnitude / (1 + y) +
      coulombMagnitude / (2 * (1 + y)^2) +
      (6 - coulombMagnitude) / 2 * y^2) =
      (fun y : ℝ => -coulombMagnitude * (1 / (1+y)) +
        coulombMagnitude * (1 / (2*(1+y)^2)) +
        (6 - coulombMagnitude) / 2 * y^2) from by funext y; ring]
  have h := (h1.const_mul (-coulombMagnitude)).add
    ((h2.const_mul coulombMagnitude).add h3)
  have heq : (fun y : ℝ => -coulombMagnitude * (1 / (1 + y)) +
      coulombMagnitude * (1 / (2 * (1 + y) ^ 2)) +
      (6 - coulombMagnitude) / 2 * y ^ 2) =
      (fun y : ℝ => -coulombMagnitude * (1 / (1 + y))) +
      ((fun y : ℝ => coulombMagnitude * (1 / (2 * (1 + y) ^ 2))) +
      (fun y : ℝ => (6 - coulombMagnitude) / 2 * y ^ 2)) := by funext y; simp only [Pi.add_apply]; ring
  rw [heq, h.deriv]
  field_simp [hne]
  ring

/-- The exact nonlinear correction to the harmonic restoring force. -/
theorem axial_gradient_remainder (x : ℝ) (hx : -1 < x) :
    axialNonlinearGradient x - 6 * x =
      -coulombMagnitude * x ^ 2 * (3 + 3 * x + x ^ 2) / (1 + x) ^ 3 := by
  have hne : 1 + x ≠ 0 := by linarith
  unfold axialNonlinearGradient
  field_simp [hne]
  ring

/-- A finite-amplitude force error, quadratic rather than cubic. -/
theorem axial_gradient_error_bound (x : ℝ) (hx : |x| ≤ (1 / 2 : ℝ)) :
    |deriv axialNonlinearPotential x - 6 * x| ≤
      40 * coulombMagnitude * |x| ^ 2 := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hx
  have hbase : (1 / 2 : ℝ) ≤ 1 + x := by linarith
  have hden : 0 < (1 + x) ^ 3 := by positivity
  have hdenlo : (1 / 8 : ℝ) ≤ (1 + x) ^ 3 := by
    calc
      (1 / 8 : ℝ) = (1 / 2 : ℝ) ^ 3 := by ring
      _ ≤ (1 + x) ^ 3 := by gcongr
  have hq : 0 ≤ 3 + 3 * x + x ^ 2 := by nlinarith [sq_nonneg x]
  have hqhi : 3 + 3 * x + x ^ 2 ≤ (5 : ℝ) := by nlinarith [sq_nonneg (x - 1 / 2)]
  have hratio : (3 + 3 * x + x ^ 2) / (1 + x) ^ 3 ≤ (40 : ℝ) := by
    apply (div_le_iff₀ hden).2
    nlinarith
  rw [axial_gradient_eq_deriv x (by linarith), axial_gradient_remainder x (by linarith)]
  have hC : 0 ≤ coulombMagnitude := le_of_lt coulomb_magnitude_positive
  calc
    |-coulombMagnitude * x ^ 2 * (3 + 3 * x + x ^ 2) / (1 + x) ^ 3| =
      coulombMagnitude * |x| ^ 2 *
        ((3 + 3 * x + x ^ 2) / (1 + x) ^ 3) := by
      rw [abs_div, abs_mul, abs_mul, abs_neg, abs_pow,
        abs_of_nonneg hC, abs_of_nonneg hq, abs_of_pos hden]
      ring
    _ ≤ coulombMagnitude * |x| ^ 2 * 40 :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = 40 * coulombMagnitude * |x| ^ 2 := by ring

end VerifiedPhysics
