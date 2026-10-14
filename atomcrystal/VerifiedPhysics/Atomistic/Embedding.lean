import VerifiedPhysics.Atomistic.MaxwellHamiltonian
import VerifiedPhysics.Atomistic.AxialSlice

namespace VerifiedPhysics.MaxwellSlab

/-- Exact geometry of the electric sites in the finite box. Vacuum has
positive z, material negative z; the interface is z=0. -/
noncomputable def siteDepth (i : ElectricSite) : ℝ :=
  if i.val < 15 then (15-(i.val : ℝ))/8 else
  if i.val < 30 then -((30-(i.val : ℝ))/8) else
  if i.val < 46 then (31-2*((i.val : ℝ)-30))/16 else
  if i.val < 62 then -((31-2*((i.val : ℝ)-46))/16) else 0

def axisPermutation (i : ElectricSite) : Equiv.Perm (Fin 3) :=
  if 30 ≤ i.val ∧ i.val < 62 then Equiv.refl _ else Equiv.swap 0 2

/-- Physical 3D positions obtained by rotating the local dipole axis and
placing its centre of mass at the declared lattice site. -/
noncomputable def globalPosition (i : ElectricSite) (r : Species → Vec3)
    (s : Species) (c : Fin 3) : ℝ :=
  (if c=2 then siteDepth i else 0) + r s (axisPermutation i c) -
    (if axisPermutation i c=2 then (1/2 : ℝ) else 0)

noncomputable def parallelPeriod : ℝ := 2*Real.pi/Real.sqrt 6

theorem physical_pair_separation (i : ElectricSite) (u : ℝ) (c : Fin 3) :
    globalPosition i (axialPositions u) .cation c -
      globalPosition i (axialPositions u) .anion c =
      if axisPermutation i c=2 then 1+u else 0 := by
  by_cases h : axisPermutation i c=2
  · simp [globalPosition, axialPositions, h]
    ring
  · simp [globalPosition, axialPositions, h]

def pairMomenta (p : ℝ) : Species → Vec3
  | .cation => fun i => if i = 2 then p else 0
  | .anion => fun i => if i = 2 then -p else 0

noncomputable def pairState (u p : ℝ) : ParticleState where
  position := axialPositions u
  momentum := pairMomenta p

theorem pair_kinetic (p : ℝ) : kinetic (pairMomenta p) = p^2/6 := by
  unfold kinetic
  rw [show (Finset.univ : Finset Species) = {.cation, .anion} from rfl]
  norm_num [pairMomenta, mass, Fin.sum_univ_three]
  ring

/-- The full finite Hamiltonian written using the original continuous 3D
positions and momenta for every pair. Coordinates are local to each fixed
lattice centre and chosen dipole axis. The field basis is explicitly finite. -/
noncomputable def particleHamiltonian (D : ElectricSite → ℝ)
    (H : MagneticSite → ℝ) (z : ElectricSite → ParticleState) : ℝ :=
  (∑ i, (D i-3*overlap i*axialDisplacement (z i).position)^2/2) +
    (∑ j, H j^2/2) +
    ∑ i, occupied i * (kinetic (z i).momentum +
      nonlinearPotential (z i).position - axialNonlinearPotential 0)

/-- The reduced finite Hamiltonian is an exact axial restriction of the
explicit 3D particle Hamiltonian. The transverse force on this slice is
zero by `axial_slice_transverse_forces`. -/
theorem particle_hamiltonian_bridge (D : ElectricSite → ℝ)
    (H : MagneticSite → ℝ) (u p : ElectricSite → ℝ)
    (hu : ∀ i, -1 < u i) :
    particleHamiltonian D H (fun i => pairState (u i) (p i)) =
      maxwellIonicHamiltonian D H u p := by
  unfold particleHamiltonian maxwellIonicHamiltonian
  simp only [pairState, axialDisplacement, axial_bond_displacement, pair_kinetic]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [nonlinear_potential_axial (u i) (hu i)]
  ring

end VerifiedPhysics.MaxwellSlab
