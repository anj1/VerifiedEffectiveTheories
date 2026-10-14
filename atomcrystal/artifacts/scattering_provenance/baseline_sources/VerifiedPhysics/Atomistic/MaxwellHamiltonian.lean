import VerifiedPhysics.Atomistic.MaxwellSlab
import VerifiedPhysics.Atomistic.NonlinearPotential

namespace VerifiedPhysics.MaxwellSlab

abbrev ElectricSite := Fin 63
abbrev MagneticSite := Fin 32

/-- 15 vacuum tangential faces, 15 material tangential faces, 16 vacuum
normal edges, 16 material normal edges, and one half-filled interface face. -/
noncomputable def filling (i : ElectricSite) : ℝ :=
  if i.val < 15 then 0 else if i.val < 30 then 1 else
  if i.val < 46 then 0 else if i.val < 62 then 1 else 1/2

/-- Squared field-mode overlap is the filling fraction. In particular the
interface contains a complete ionic pair, with overlap 1/sqrt(2), not half
an ion. Physical pair masses and charges remain 6 and ±3. -/
noncomputable def overlap (i : ElectricSite) : ℝ := Real.sqrt (filling i)

def occupied (i : ElectricSite) : ℝ :=
  if i.val < 15 then 0 else if i.val < 30 then 1 else
  if i.val < 46 then 0 else 1

/-- The actual finite curl incidence matrix: normal mesh spacing 1/8,
parallel Fourier wave number sqrt(6), and omitted (zero) tangential electric
degrees of freedom at both conducting exterior faces. -/
noncomputable def curlMatrix (j : MagneticSite) (i : ElectricSite) : ℝ :=
  if i.val < 15 then
    if j.val = i.val then -8 else if j.val = i.val+1 then 8 else 0
  else if i.val < 30 then
    if j.val = i.val+1 then -8 else if j.val = i.val+2 then 8 else 0
  else if i.val < 62 then
    if j.val+30 = i.val then Real.sqrt 6 else 0
  else if j.val = 15 then 8 else if j.val = 31 then -8 else 0

/-- Finite nonlinear Hamiltonian in electric displacement, magnetic field,
ionic displacement and momentum coordinates. Vacuum sites have no ion and
their momentum is fixed to zero. The polarization coupling is explicitly
inside `(D-P)^2/2`, including its quadratic self-energy. -/
noncomputable def maxwellIonicHamiltonian
    (D : ElectricSite → ℝ) (H : MagneticSite → ℝ)
    (u p : ElectricSite → ℝ) : ℝ :=
  (∑ i, (D i - 3*overlap i*u i)^2/2) + (∑ j, H j^2/2) +
    ∑ i, occupied i * (p i^2/6 +
      (axialNonlinearPotential (u i) - axialNonlinearPotential 0))

theorem filling_nonnegative (i : ElectricSite) : 0 ≤ filling i := by
  unfold filling
  split_ifs <;> norm_num

theorem occupied_nonnegative (i : ElectricSite) : 0 ≤ occupied i := by
  unfold occupied
  split_ifs <;> norm_num

theorem overlap_sq (i : ElectricSite) : overlap i ^ 2 = filling i :=
  Real.sq_sqrt (filling_nonnegative i)

/-- The infinitesimal energy at stiffness b is positive semidefinite,
including the full field-polarization coupling. -/
noncomputable def quadraticEnergy (b : ℝ) (D : ElectricSite → ℝ)
    (H : MagneticSite → ℝ) (u v : ElectricSite → ℝ) : ℝ :=
  (∑ i, (D i-3*overlap i*u i)^2/2) + (∑ j, H j^2/2) +
    ∑ i, occupied i * (3*v i^2/2 + 3*b*u i^2/2)

theorem quadratic_energy_nonnegative (b : ℝ) (hb : 0 ≤ b)
    (D : ElectricSite → ℝ) (H : MagneticSite → ℝ) (u v : ElectricSite → ℝ) :
    0 ≤ quadraticEnergy b D H u v := by
  unfold quadraticEnergy
  apply add_nonneg
  · positivity
  · apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (occupied_nonnegative i) (by positivity)

/-- Summation by parts for the declared finite curl and its transpose. -/
theorem curl_adjoint (E : ElectricSite → ℝ) (H : MagneticSite → ℝ) :
    (∑ i, E i * ∑ j, curlMatrix j i * H j) =
      ∑ j, H j * ∑ i, curlMatrix j i * E i := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Exact closed-system energy balance. Maxwell gives E-dot=CᵀH-3gv and
H-dot=-CE; occupied ionic sites obey 3a=-U'(u)+3gE. No damping or source term is
hidden in the field equations. This holds for the nonlinear force as well
as for its certified Hessian. -/
theorem closed_maxwell_ionic_energy_balance
    (E : ElectricSite → ℝ) (H : MagneticSite → ℝ)
    (v a g : ElectricSite → ℝ)
    (hion : ∀ i, occupied i * (3*a i + g i) = 3*overlap i*E i) :
    (∑ i, E i * ((∑ j, curlMatrix j i * H j)-3*overlap i*v i)) +
      (∑ j, H j * (-(∑ i, curlMatrix j i * E i))) +
      (∑ i, occupied i * (3*v i*a i + g i*v i)) = 0 := by
  have hi : (∑ i, occupied i*(3*v i*a i+g i*v i)) =
      ∑ i, E i*(3*overlap i*v i) := by
    apply Finset.sum_congr rfl
    intro i _
    have h := congrArg (fun t : ℝ => v i*t) (hion i)
    nlinarith
  rw [hi]
  simp_rw [mul_sub, Finset.sum_sub_distrib, mul_neg, Finset.sum_neg_distrib]
  rw [curl_adjoint]
  ring

noncomputable def electricVector (f : Fields) (i : ElectricSite) : ℝ :=
  if i.val < 15 then f.vacuumE i.val else
  if i.val < 30 then f.materialE (i.val-15) else
  if i.val < 46 then Real.sqrt 6 * f.vacuumH (i.val-30) else
  if i.val < 62 then Real.sqrt 6 * f.normalE (i.val-46) else f.interfaceE

noncomputable def ionicVector (f : Fields) (i : ElectricSite) : ℝ :=
  if i.val < 15 then 0 else if i.val < 30 then f.tangentialIon (i.val-15) else
  if i.val < 46 then 0 else if i.val < 62 then Real.sqrt 6*f.normalIon (i.val-46)
  else f.interfaceIon

noncomputable def magneticVector (f : Fields) (j : MagneticSite) : ℝ :=
  if j.val < 16 then f.vacuumH j.val else f.materialH (j.val-16)

end VerifiedPhysics.MaxwellSlab
