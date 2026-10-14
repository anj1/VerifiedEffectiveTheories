import VerifiedPhysics.Atomistic.LinearDynamics

/-!
A nonlinear pair model giving the harmonic axial bond as its quadratic
equilibrium expansion. The Coulomb coefficient is fixed by charges ±3,
vacuum permittivity 1, and the factor `1/(4π)`. A repulsive inverse-square
term and a further radial short-range quadratic term make the equilibrium
curvature exactly six. Collisions are excluded by `AdmissiblePosition`.

This file certifies the axial expansion. It does not bound the response of a
finite-amplitude driven nonlinear trajectory; later response theorems are
therefore explicitly about the linearized model.
-/

namespace VerifiedPhysics

noncomputable def coulombMagnitude : ℝ :=
  -(charge .cation * charge .anion) /
    (4 * Real.pi * vacuumPermittivity)

theorem coulomb_magnitude_eq : coulombMagnitude = 9 / (4 * Real.pi) := by
  norm_num [coulombMagnitude, charge, vacuumPermittivity]

theorem coulomb_magnitude_positive : 0 < coulombMagnitude := by
  rw [coulomb_magnitude_eq]
  positivity

theorem coulomb_magnitude_lt_one : coulombMagnitude < 1 := by
  rw [coulomb_magnitude_eq]
  have hden : (0 : ℝ) < 4 * Real.pi := by positivity
  apply (div_lt_iff₀ hden).2
  nlinarith [Real.pi_gt_three]

noncomputable def bondLength (r : Species → Vec3) : ℝ :=
  Real.sqrt (∑ i : Fin 3, (r .cation i - r .anion i) ^ 2)

def AdmissiblePosition (r : Species → Vec3) : Prop := 0 < bondLength r

/-- Explicit Coulomb, inverse-square repulsion and radial short-range term;
the last term stabilizes transverse relative displacements. -/
noncomputable def nonlinearPotential (r : Species → Vec3) : ℝ :=
  -coulombMagnitude / bondLength r +
    coulombMagnitude / (2 * bondLength r ^ 2) +
    ((6 - coulombMagnitude) / 2) * (bondLength r - 1) ^ 2 +
    3 * ((r .cation 0 - r .anion 0) ^ 2 +
      (r .cation 1 - r .anion 1) ^ 2)

noncomputable def nonlinearHamiltonian (z : ParticleState) (E : ℝ) : ℝ :=
  kinetic z.momentum + nonlinearPotential z.position +
    emEnergy E + couplingEnergy z.position E

theorem nonlinear_equilibrium_energy :
    nonlinearPotential equilibrium = -coulombMagnitude / 2 := by
  norm_num [nonlinearPotential, bondLength, equilibrium,
    Fin.sum_univ_three]
  ring

/-- Mechanical stability of the collision-free nonlinear two-ion potential
modulo center-of-mass translations. -/
theorem nonlinear_potential_stable (r : Species → Vec3)
    (hr : AdmissiblePosition r) :
    nonlinearPotential equilibrium ≤ nonlinearPotential r := by
  have hd : bondLength r ≠ 0 := ne_of_gt hr
  have hC : 0 ≤ coulombMagnitude := le_of_lt coulomb_magnitude_positive
  have hS : 0 ≤ (6 - coulombMagnitude) / 2 := by
    linarith [coulomb_magnitude_lt_one]
  have hrewrite : nonlinearPotential r - nonlinearPotential equilibrium =
      coulombMagnitude * (bondLength r - 1) ^ 2 /
        (2 * bondLength r ^ 2) +
      ((6 - coulombMagnitude) / 2) * (bondLength r - 1) ^ 2 +
      3 * ((r .cation 0 - r .anion 0) ^ 2 +
        (r .cation 1 - r .anion 1) ^ 2) := by
    rw [nonlinear_equilibrium_energy]
    unfold nonlinearPotential
    field_simp [hd]
    ring
  have hnonneg : 0 ≤ nonlinearPotential r - nonlinearPotential equilibrium := by
    rw [hrewrite]
    positivity
  linarith

noncomputable def axialNonlinearPotential (x : ℝ) : ℝ :=
  -coulombMagnitude / (1 + x) +
    coulombMagnitude / (2 * (1 + x) ^ 2) +
    ((6 - coulombMagnitude) / 2) * x ^ 2

theorem bond_length_axial (x : ℝ) (hx : -1 < x) :
    bondLength (axialPositions x) = 1 + x := by
  have hp : 0 ≤ 1 + x := by linarith
  simp [bondLength, Fin.sum_univ_three, axialPositions]
  have heq : 1 + x / 2 - -x / 2 = 1 + x := by ring
  rw [heq, Real.sqrt_sq_eq_abs, abs_of_nonneg hp]

theorem nonlinear_potential_axial (x : ℝ) (hx : -1 < x) :
    nonlinearPotential (axialPositions x) = axialNonlinearPotential x := by
  simp [nonlinearPotential, axialNonlinearPotential,
    bond_length_axial x hx, axialPositions]

/-- Exact cubic remainder; its vanishing through second order is the
lower-to-linearized bridge used by the optical response model. -/
theorem axial_nonlinear_expansion (x : ℝ) (hx : -1 < x) :
    axialNonlinearPotential x =
      axialNonlinearPotential 0 + axialPotential x -
        coulombMagnitude * x ^ 3 * (2 + x) / (2 * (1 + x) ^ 2) := by
  have hden : 1 + x ≠ 0 := by linarith
  unfold axialNonlinearPotential axialPotential
  field_simp
  ring

theorem full_to_linearized_axial_bridge (x : ℝ) (hx : -1 < x) :
    nonlinearPotential (axialPositions x) -
      nonlinearPotential (axialPositions 0) =
      potential (axialPositions x) -
        coulombMagnitude * x ^ 3 * (2 + x) / (2 * (1 + x) ^ 2) := by
  rw [nonlinear_potential_axial x hx,
    nonlinear_potential_axial 0 (by norm_num), axial_nonlinear_expansion x hx,
    axial_potential_bridge]
  ring

noncomputable def axialLinearizationError (x : ℝ) : ℝ :=
  coulombMagnitude * x ^ 3 * (2 + x) / (2 * (1 + x) ^ 2)

/-- A deterministic finite-displacement Taylor error bound for the nonlinear
pair potential, in the interval `|x| ≤ 1/2`. -/
theorem axial_linearization_error_bound (x : ℝ) (hx : |x| ≤ (1 / 2 : ℝ)) :
    |axialLinearizationError x| ≤
      5 * coulombMagnitude * |x| ^ 3 := by
  obtain ⟨hxlo, hxhi⟩ := abs_le.mp hx
  have hbase : (1 / 2 : ℝ) ≤ 1 + x := by linarith
  have hnum : 0 ≤ 2 + x := by linarith
  have hnumhi : 2 + x ≤ (5 / 2 : ℝ) := by linarith
  have hquad : (1 / 4 : ℝ) ≤ (1 + x) ^ 2 := by nlinarith
  have hden : 0 < 2 * (1 + x) ^ 2 := by positivity
  have hratio : (2 + x) / (2 * (1 + x) ^ 2) ≤ (5 : ℝ) := by
    apply (div_le_iff₀ hden).2
    nlinarith [hquad, hnumhi]
  have hC : 0 ≤ coulombMagnitude := le_of_lt coulomb_magnitude_positive
  calc
    |axialLinearizationError x| =
        coulombMagnitude * |x| ^ 3 * ((2 + x) / (2 * (1 + x) ^ 2)) := by
      unfold axialLinearizationError
      rw [abs_div, abs_mul, abs_mul, abs_pow,
        abs_of_nonneg hC, abs_of_nonneg hnum, abs_of_pos hden]
      ring
    _ ≤ coulombMagnitude * |x| ^ 3 * 5 :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = 5 * coulombMagnitude * |x| ^ 3 := by ring

theorem full_to_linearized_axial_bound (x : ℝ)
    (hx : |x| ≤ (1 / 2 : ℝ)) :
    |nonlinearPotential (axialPositions x) -
      nonlinearPotential (axialPositions 0) -
      potential (axialPositions x)| ≤
      5 * coulombMagnitude * |x| ^ 3 := by
  have hx' : -1 < x := by
    have := (abs_le.mp hx).1
    linarith
  rw [full_to_linearized_axial_bridge x hx']
  have heq : potential (axialPositions x) -
      coulombMagnitude * x ^ 3 * (2 + x) / (2 * (1 + x) ^ 2) -
      potential (axialPositions x) = -axialLinearizationError x := by
    unfold axialLinearizationError
    ring
  rw [heq]
  rw [abs_neg]
  exact axial_linearization_error_bound x hx

/-- The explicit domain and deterministic error budget for the axial
full-potential to harmonic-potential abstraction. -/
def AxialLinearizationBound : Prop :=
  ∀ x : ℝ, |x| ≤ (1 / 2 : ℝ) →
    |nonlinearPotential (axialPositions x) -
      nonlinearPotential (axialPositions 0) -
      potential (axialPositions x)| ≤
      5 * coulombMagnitude * |x| ^ 3

theorem certified_axial_linearization : AxialLinearizationBound := by
  intro x hx
  exact full_to_linearized_axial_bound x hx

end VerifiedPhysics
