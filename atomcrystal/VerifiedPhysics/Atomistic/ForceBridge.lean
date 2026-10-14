import VerifiedPhysics.Atomistic.AxialForce
import VerifiedPhysics.Experiments.SlabMode

namespace VerifiedPhysics

/-! The same nonlinear pair potential is now used independently in both
ionic layers; the quadratic field and termination terms remain explicit. -/

noncomputable def nonlinearSlabPotential (k2 x0 x1 : ℝ) : ℝ :=
  axialNonlinearPotential x0 + axialNonlinearPotential x1 +
    (k2 / 2) * (x0 - x1) ^ 2 + (k2 / 4) * x1 ^ 2

noncomputable def nonlinearSlabGradient0 (k2 x0 x1 : ℝ) : ℝ :=
  axialNonlinearGradient x0 + k2 * (x0 - x1)

noncomputable def nonlinearSlabGradient1 (k2 x0 x1 : ℝ) : ℝ :=
  axialNonlinearGradient x1 - k2 * (x0 - x1) + (k2 / 2) * x1

theorem nonlinear_slab_gradient_bridge (k2 x0 x1 : ℝ)
    (h0 : -1 < x0) (h1 : -1 < x1) :
    deriv (fun y => nonlinearSlabPotential k2 y x1) x0 =
      nonlinearSlabGradient0 k2 x0 x1 ∧
    deriv (fun y => nonlinearSlabPotential k2 x0 y) x1 =
      nonlinearSlabGradient1 k2 x0 x1 := by
  constructor
  · have hf : (fun y : ℝ => nonlinearSlabPotential k2 y x1) =
        axialNonlinearPotential +
          (fun y : ℝ => (k2 / 2) * (y - x1) ^ 2 +
            (axialNonlinearPotential x1 + (k2 / 4) * x1 ^ 2)) := by
      funext y; dsimp [nonlinearSlabPotential]; ring
    have hp0 : 0 < 1 + x0 := by linarith
    rw [hf, deriv_add (by unfold axialNonlinearPotential; fun_prop (disch := positivity)) (by fun_prop)]
    rw [axial_gradient_eq_deriv x0 h0]
    have hp : deriv (fun y : ℝ => (k2 / 2) * (y - x1) ^ 2 +
        (axialNonlinearPotential x1 + (k2 / 4) * x1 ^ 2)) x0 =
        k2 * (x0 - x1) := by
      have hg : (fun y : ℝ => (k2 / 2) * (y - x1) ^ 2 +
          (axialNonlinearPotential x1 + (k2 / 4) * x1 ^ 2)) =
          (fun y : ℝ => (k2 / 2) * y ^ 2 + (-k2 * x1) * y) +
          (fun _ : ℝ => axialNonlinearPotential x1 + (3 * k2 / 4) * x1 ^ 2) := by
        funext y; dsimp; ring
      rw [hg, deriv_add (by fun_prop) (by fun_prop), deriv_const]
      change deriv ((fun y : ℝ => (k2 / 2) * y ^ 2) +
        (fun y : ℝ => (-k2 * x1) * y)) x0 + 0 = _
      rw [deriv_add (by fun_prop) (by fun_prop), deriv_const_mul_field,
        deriv_pow_field, deriv_const_mul_id]
      ring
    rw [hp]
    rfl
  · have hf : (fun y : ℝ => nonlinearSlabPotential k2 x0 y) =
        axialNonlinearPotential +
          (fun y : ℝ => (k2 / 2) * (x0 - y) ^ 2 +
            (k2 / 4) * y ^ 2 + axialNonlinearPotential x0) := by
      funext y; dsimp [nonlinearSlabPotential]; ring
    have hp1 : 0 < 1 + x1 := by linarith
    rw [hf, deriv_add (by unfold axialNonlinearPotential; fun_prop (disch := positivity)) (by fun_prop)]
    rw [axial_gradient_eq_deriv x1 h1]
    have hp : deriv (fun y : ℝ => (k2 / 2) * (x0 - y) ^ 2 +
        (k2 / 4) * y ^ 2 + axialNonlinearPotential x0) x1 =
        -k2 * (x0 - x1) + (k2 / 2) * x1 := by
      have hg : (fun y : ℝ => (k2 / 2) * (x0 - y) ^ 2 +
          (k2 / 4) * y ^ 2 + axialNonlinearPotential x0) =
          (fun y : ℝ => (3 * k2 / 4) * y ^ 2 + (-k2 * x0) * y) +
          (fun _ : ℝ => axialNonlinearPotential x0 + (k2 / 2) * x0 ^ 2) := by
        funext y; dsimp; ring
      rw [hg, deriv_add (by fun_prop) (by fun_prop), deriv_const]
      change deriv ((fun y : ℝ => (3 * k2 / 4) * y ^ 2) +
        (fun y : ℝ => (-k2 * x0) * y)) x1 + 0 = _
      rw [deriv_add (by fun_prop) (by fun_prop), deriv_const_mul_field,
        deriv_pow_field, deriv_const_mul_id]
      ring
    rw [hp]
    dsimp [nonlinearSlabGradient1]
    ring

/-- Deterministic nonlinear-to-harmonic slab force bound. `reducedMass *
slabOperator` is the harmonic potential gradient, so this connects the
nonlinear potential directly to the operator used in the surface test. -/
theorem nonlinear_to_harmonic_surface_bound (k2 x0 x1 : ℝ)
    (h0 : |x0| ≤ (1 / 2 : ℝ)) (h1 : |x1| ≤ (1 / 2 : ℝ)) :
    |deriv (fun y => nonlinearSlabPotential k2 y x1) x0 -
      reducedMass * slabOperator0 k2 x0 x1| ≤
        40 * coulombMagnitude * |x0| ^ 2 ∧
    |deriv (fun y => nonlinearSlabPotential k2 x0 y) x1 -
      reducedMass * slabOperator1 k2 x0 x1| ≤
        40 * coulombMagnitude * |x1| ^ 2 := by
  have hb := nonlinear_slab_gradient_bridge k2 x0 x1
    (by have := (abs_le.mp h0).1; linarith)
    (by have := (abs_le.mp h1).1; linarith)
  constructor
  · rw [hb.1]
    have heq : nonlinearSlabGradient0 k2 x0 x1 -
        reducedMass * slabOperator0 k2 x0 x1 =
        axialNonlinearGradient x0 - 6 * x0 := by
      dsimp [nonlinearSlabGradient0, slabOperator0, reducedMass]; ring
    rw [heq, ← axial_gradient_eq_deriv x0 (by have := (abs_le.mp h0).1; linarith)]
    exact axial_gradient_error_bound x0 h0
  · rw [hb.2]
    have heq : nonlinearSlabGradient1 k2 x0 x1 -
        reducedMass * slabOperator1 k2 x0 x1 =
        axialNonlinearGradient x1 - 6 * x1 := by
      dsimp [nonlinearSlabGradient1, slabOperator1, reducedMass]; ring
    rw [heq, ← axial_gradient_eq_deriv x1 (by have := (abs_le.mp h1).1; linarith)]
    exact axial_gradient_error_bound x1 h1

end VerifiedPhysics
