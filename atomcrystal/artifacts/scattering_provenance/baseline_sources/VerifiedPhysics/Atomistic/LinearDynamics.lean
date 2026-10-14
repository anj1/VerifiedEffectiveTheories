import VerifiedPhysics.Base.Model

namespace VerifiedPhysics

/-- Axial potential after the center of mass and transverse coordinates have
been held fixed. -/
def axialPotential (x : ℝ) : ℝ := 3 * x ^ 2

def axialForce (x : ℝ) : ℝ := -6 * x

theorem axial_potential_bridge (x : ℝ) :
    potential (axialPositions x) = axialPotential x := by
  rw [potential_on_axial_slice]
  rfl

noncomputable def axialCoupledPotential (x E : ℝ) : ℝ :=
  axialPotential x + emEnergy E + couplingEnergy (axialPositions x) E

theorem axial_coupling_bridge (x E : ℝ) :
    couplingEnergy (axialPositions x) E = -3 * x * E := by
  simp [couplingEnergy, axialDisplacement, axial_bond_displacement, charge]

theorem force_is_negative_gradient (x : ℝ) :
    axialForce x = -deriv axialPotential x := by
  unfold axialForce axialPotential
  rw [deriv_const_mul_field, deriv_pow_field]
  ring

/-- Axial Hessian on the translation-free relative-coordinate subspace. -/
def restrictedHessian : ℝ := 6

theorem restricted_hessian_positive : 0 < restrictedHessian := by
  norm_num [restrictedHessian]

theorem restricted_quadratic_nonnegative (x : ℝ) :
    0 ≤ restrictedHessian * x ^ 2 := by
  unfold restrictedHessian
  positivity

/-- The Cartesian Hessian of the harmonic bond, with translational zero modes
excluded by the relative-coordinate representation. -/
def bondHessian (i j : Fin 3) : ℝ := if i = j then 6 else 0

theorem bond_hessian_symmetric (i j : Fin 3) :
    bondHessian i j = bondHessian j i := by
  by_cases h : i = j
  · subst j; simp [bondHessian]
  · have h' : j ≠ i := Ne.symm h
    simp [bondHessian, h, h']

/-- Force on each ion along the polar axis, including electric coupling. -/
def cationForce (x E : ℝ) : ℝ := -6 * x + 3 * E
def anionForce (x E : ℝ) : ℝ := 6 * x - 3 * E

theorem driven_force_is_negative_gradient (x E : ℝ) :
    cationForce x E = -deriv (fun y => axialCoupledPotential y E) x := by
  have hf : (fun y : ℝ => axialCoupledPotential y E) =
      (fun y : ℝ => (3 * y ^ 2 + (-3 * E) * y) + emEnergy E) := by
    funext y
    dsimp [axialCoupledPotential, axialPotential]
    rw [axial_coupling_bridge]
    ring
  rw [hf, deriv_add_const]
  change cationForce x E = -deriv ((fun y : ℝ => 3 * y ^ 2) +
    (fun y : ℝ => (-3 * E) * y)) x
  rw [deriv_add (by fun_prop) (by fun_prop)]
  rw [deriv_const_mul_field, deriv_pow_field, deriv_const_mul_id]
  dsimp [cationForce]
  ring

/-- Subtracting the two six-mass equations gives the optical equation. -/
theorem relative_equation (x E aPlus aMinus : ℝ)
    (hp : 6 * aPlus = cationForce x E)
    (hm : 6 * aMinus = anionForce x E) :
    reducedMass * (aPlus - aMinus) =
      -spring * x + charge .cation * E := by
  dsimp [reducedMass, spring, charge, cationForce, anionForce] at *
  linarith

/-- Algebraic energy balance for the closed, unforced lossless optical mode.
Here `v` and `a` are instantaneous velocity and acceleration. -/
theorem closed_energy_rate_zero (x v a : ℝ)
    (h : reducedMass * a = -spring * x) :
    reducedMass * v * a + spring * x * v = 0 := by
  dsimp [reducedMass, spring] at *
  calc
    3 * v * a + 6 * x * v = (3 * a + 6 * x) * v := by ring
    _ = 0 := by rw [show 3 * a + 6 * x = 0 by linarith]; ring

end VerifiedPhysics
