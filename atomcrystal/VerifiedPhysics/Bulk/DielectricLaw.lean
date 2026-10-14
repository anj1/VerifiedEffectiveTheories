import VerifiedPhysics.Atomistic.LinearDynamics

namespace VerifiedPhysics

/-- `s` is squared angular frequency. The forced optical-coordinate equation
is the Fourier transform of the two-ion Newton equations. -/
def MicroResponse (s E x : ℝ) : Prop :=
  (spring - reducedMass * s) * x = charge .cation * E

/-- Polarization of one unit cell of volume one. -/
noncomputable def polarization (x : ℝ) : ℝ := charge .cation * x / cellVolume

/-- Candidate discovered from bulk response samples, then proved below. -/
noncomputable def dielectric (s : ℝ) : ℝ := (5 - s) / (2 - s)

def bulkDomain (s : ℝ) : Prop := 0 ≤ s ∧ s ≠ 2

/-- The exact zero-error lower-to-higher response statement. -/
def BulkDielectricLawHolds : Prop :=
  ∀ s E x : ℝ, bulkDomain s → MicroResponse s E x →
    polarization x = vacuumPermittivity * (dielectric s - 1) * E

theorem exact_bulk_dielectric_law : BulkDielectricLawHolds := by
  intro s E x hs hresponse
  have hden : 2 - s ≠ 0 := by
    intro h
    have : s = 2 := by linarith
    exact hs.2 this
  have hx : (2 - s) * x = E := by
    dsimp [MicroResponse, spring, reducedMass, charge] at hresponse
    linarith
  have heps : dielectric s - 1 = 3 / (2 - s) := by
    unfold dielectric
    field_simp
    ring
  rw [heps]
  dsimp [polarization, charge, cellVolume, vacuumPermittivity]
  simp only [div_one, one_mul]
  calc
    3 * x = (3 / (2 - s)) * ((2 - s) * x) := by
      field_simp
    _ = (3 / (2 - s)) * E := by rw [hx]

theorem optical_frequency_squared : spring / reducedMass = 2 := by
  norm_num [spring, reducedMass]

end VerifiedPhysics
