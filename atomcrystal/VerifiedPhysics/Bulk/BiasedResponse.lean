import VerifiedPhysics.Atomistic.BiasedHessian
import VerifiedPhysics.Atomistic.MaxwellSlab
import VerifiedPhysics.Bulk.DielectricLaw

namespace VerifiedPhysics

/-- A nonzero transverse optical displacement at s=2, with stiffness derived
from the nonlinear potential, and the longitudinal s=5 mode obtained by
imposing the zero-displacement-field Gauss constraint E+P=0. -/
theorem microscopic_optical_modes :
    (deriv (deriv axialNonlinearPotential) 0 - reducedMass*2)*1 = 0 ∧
    (deriv (deriv axialNonlinearPotential) 0 - reducedMass*5)*1 = 3*(-3) ∧
    (-3 : ℝ) + 3*1 = 0 := by
  rw [microscopic_bulk_hessian]
  norm_num [spring, reducedMass]

/-- Linear response about a force-balanced microscopic bias. The spring
coefficient is the second derivative of the nonlinear ionic potential. -/
def HessianResponse (a s E x : ℝ) : Prop :=
  (deriv (deriv axialNonlinearPotential) a - reducedMass * s) * x = 3 * E

theorem hessian_susceptibility (a s E x : ℝ) (ha : -1 < a)
    (hs : biasedStiffness a - s ≠ 0) (hr : HessianResponse a s E x) :
    3 * x = (MaxwellSlab.eps (biasedStiffness a) s - 1) * E := by
  have he : (biasedStiffness a - s) * x = E := by
    unfold HessianResponse at hr
    rw [nonlinear_second_derivative a ha] at hr
    dsimp [reducedMass] at hr
    nlinarith
  unfold MaxwellSlab.eps
  rw [add_sub_cancel_left]
  rw [← he]
  field_simp [hs]

theorem dielectric_stiffness_error (b s : ℝ)
    (hb : b ∈ Set.Icc (1999999/1000000 : ℝ) (2000001/1000000 : ℝ))
    (hs : s ∈ Set.Icc (3.01 : ℝ) 3.012) :
    |MaxwellSlab.eps b s - dielectric s| ≤ (3/1000000 : ℝ) := by
  have hd : b-s < -1 := by linarith [hb.2, hs.1]
  have ht : 2-s < -1 := by linarith [hs.1]
  have hn : b-s ≠ 0 := by linarith
  have hn' : 2-s ≠ 0 := by linarith
  have heq : MaxwellSlab.eps b s - dielectric s =
      3 * (2-b) / ((b-s)*(2-s)) := by
    unfold MaxwellSlab.eps dielectric
    field_simp [hn, hn']
    ring
  have hprod : 1 ≤ (b-s)*(2-s) := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ s-b-1) (by linarith : 0 ≤ s-3)]
  have hp : 0 < (b-s)*(2-s) := by linarith
  rw [heq, abs_div, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<3), abs_of_pos hp]
  apply (div_le_iff₀ hp).2
  have ha : |2-b| ≤ (1/1000000 : ℝ) := by
    rw [abs_le]
    constructor <;> linarith [hb.1, hb.2]
  nlinarith

/-- Nonzero deterministic constitutive error propagated from the microscopic
Hessian interval. This is a linear-response theorem about biased equilibria. -/
theorem microscopic_bulk_response_error (a s E x : ℝ)
    (ha : |a| ≤ (1/1000000000 : ℝ))
    (hs : s ∈ Set.Icc (3.01 : ℝ) 3.012)
    (hr : HessianResponse a s E x) :
    |3*x - (dielectric s - 1)*E| ≤ (3/1000000 : ℝ) * |E| := by
  have hb := microscopic_stiffness_interval a ha
  have hane : -1 < a := by have := (abs_le.mp ha).1; linarith
  have hne : biasedStiffness a - s ≠ 0 := by linarith [hb.2, hs.1]
  rw [hessian_susceptibility a s E x hane hne hr]
  have heq : (MaxwellSlab.eps (biasedStiffness a) s - 1)*E - (dielectric s-1)*E =
      (MaxwellSlab.eps (biasedStiffness a) s - dielectric s)*E := by ring
  rw [heq, abs_mul]
  exact mul_le_mul_of_nonneg_right (dielectric_stiffness_error _ _ hb hs) (abs_nonneg _)

end VerifiedPhysics
