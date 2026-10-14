import Mathlib

/-!
# Exact dimensionless rigid-ion model

Two ions of opposite charge occupy each cell. Coordinates and momenta are
continuous in three dimensions. Length, mass, charge, time and permittivity
are dimensionless; their values below are *assumptions*, not NaCl data.

The potential is a harmonic ionic bond about its reference separation. This
is an exact finite model, not a proof that a Coulomb/Born-Mayer potential has
this Hessian. There is no electronic polarizability, dissipation or thermal MD.
-/

namespace VerifiedPhysics

abbrev Vec3 := Fin 3 → ℝ

inductive Species where
  | cation
  | anion
  deriving DecidableEq

instance : Fintype Species where
  elems := {.cation, .anion}
  complete := by intro x; cases x <;> simp

def mass : Species → ℝ
  | .cation => 6
  | .anion => 6

def charge : Species → ℝ
  | .cation => 3
  | .anion => -3

structure ParticleState where
  position : Species → Vec3
  momentum : Species → Vec3

def referenceBond (i : Fin 3) : ℝ := if i = 2 then 1 else 0

def bondDisplacement (r : Species → Vec3) (i : Fin 3) : ℝ :=
  r .cation i - r .anion i - referenceBond i

def potential (r : Species → Vec3) : ℝ :=
  3 * ∑ i : Fin 3, (bondDisplacement r i) ^ 2

noncomputable def kinetic (p : Species → Vec3) : ℝ :=
  ∑ s : Species, (∑ i : Fin 3, (p s i) ^ 2) / (2 * mass s)

noncomputable def hamiltonian (z : ParticleState) : ℝ :=
  kinetic z.momentum + potential z.position

def equilibrium : Species → Vec3
  | .cation => fun i => if i = 2 then 1 else 0
  | .anion => fun _ => 0

theorem equilibrium_bond (i : Fin 3) : bondDisplacement equilibrium i = 0 := by
  simp [bondDisplacement, equilibrium, referenceBond]

theorem equilibrium_potential : potential equilibrium = 0 := by
  simp [potential, equilibrium_bond]

theorem potential_nonnegative (r : Species → Vec3) : 0 ≤ potential r := by
  unfold potential
  positivity

/-- Center-of-mass-fixed axial slice through the continuous 3D configuration
space. The transverse coordinates remain zero. -/
noncomputable def axialPositions (x : ℝ) : Species → Vec3
  | .cation => fun i => if i = 2 then 1 + x / 2 else 0
  | .anion => fun i => if i = 2 then -x / 2 else 0

theorem axial_bond_displacement (x : ℝ) :
    bondDisplacement (axialPositions x) 2 = x := by
  norm_num [bondDisplacement, axialPositions, referenceBond]
  ring

theorem potential_on_axial_slice (x : ℝ) :
    potential (axialPositions x) = 3 * x ^ 2 := by
  simp [potential, Fin.sum_univ_three, bondDisplacement,
    axialPositions, referenceBond]
  ring

/-- One pair's axial optical displacement. -/
def axialDisplacement (r : Species → Vec3) : ℝ := bondDisplacement r 2

/-- The exact reduced mass for two ions of mass six. -/
def reducedMass : ℝ := 3

/-- The exact axial spring coefficient in `U = spring*x²/2`. -/
def spring : ℝ := 6

/-- Unit cell volume, vacuum permittivity, and light speed are each one. -/
def cellVolume : ℝ := 1
def vacuumPermittivity : ℝ := 1
def lightSpeed : ℝ := 1

/-- One real longitudinal electric-field amplitude with quadratic vacuum
energy. The source that maintains a monochromatic field is external. -/
noncomputable def emEnergy (E : ℝ) : ℝ :=
  vacuumPermittivity * E ^ 2 / 2

/-- Dipolar energy of the charged pair in that field. -/
noncomputable def couplingEnergy (r : Species → Vec3) (E : ℝ) : ℝ :=
  -charge .cation * axialDisplacement r * E

noncomputable def coupledHamiltonian (z : ParticleState) (E : ℝ) : ℝ :=
  hamiltonian z + emEnergy E + couplingEnergy z.position E

end VerifiedPhysics
