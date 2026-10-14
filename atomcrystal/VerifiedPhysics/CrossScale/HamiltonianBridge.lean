import VerifiedPhysics.Atomistic.MaxwellHamiltonian
import VerifiedPhysics.Atomistic.BiasedHessian

namespace VerifiedPhysics.MaxwellSlab

/-- The biased finite Hamiltonian used by the final theorem. Each occupied
site is a complete pair; `u` and `p` are physical ionic coordinates. -/
noncomputable def biasedHamiltonian (a : ℝ)
    (D : ElectricSite → ℝ) (H : MagneticSite → ℝ)
    (u p : ElectricSite → ℝ) : ℝ :=
  (∑ i, (D i-3*overlap i*u i)^2/2) + (∑ j, H j^2/2) +
    ∑ i, occupied i * (p i^2/6 + forceBalancedPotential a (u i))

noncomputable def localCoupledPotential (a g D x : ℝ) : ℝ :=
  forceBalancedPotential a x + (D-3*g*x)^2/2

theorem electric_energy_derivative (g D x : ℝ) :
    deriv (fun y : ℝ => (D-3*g*y)^2/2) x = -3*g*(D-3*g*x) := by
  have hf : (fun y : ℝ => (D-3*g*y)^2/2) =
      (fun y : ℝ => ((9*g^2/2)*y^2 + (-3*g*D)*y) + D^2/2) := by
    funext y; ring
  rw [hf, deriv_add_const]
  change deriv ((fun y : ℝ => (9*g^2/2)*y^2) + (fun y : ℝ => (-3*g*D)*y)) x = _
  rw [deriv_add (by fun_prop) (by fun_prop), deriv_const_mul_field,
    deriv_pow_field, deriv_const_mul_id]
  ring

/-- The ionic force in the Maxwell model is the gradient of its Hamiltonian
potential. The electric force uses the actual field `E=D-P`. -/
theorem local_coupled_force (a g D x : ℝ) (ha : -1 < a+x) :
    -deriv (localCoupledPotential a g D) x =
      -(axialNonlinearGradient (a+x)-axialNonlinearGradient a) + 3*g*(D-3*g*x) := by
  have hp : 0 < 1+(a+x) := by linarith
  have hd : DifferentiableAt ℝ (forceBalancedPotential a) x := by
    unfold forceBalancedPotential axialNonlinearPotential
    fun_prop (disch := positivity)
  change -deriv ((forceBalancedPotential a) + (fun y : ℝ => (D-3*g*y)^2/2)) x = _
  rw [deriv_add hd (by fun_prop), force_balanced_derivative a x ha,
    electric_energy_derivative]
  ring

end VerifiedPhysics.MaxwellSlab
