import VerifiedPhysics.Atomistic.MaxwellHamiltonian

namespace VerifiedPhysics.GratingExperiment

/-- Independently specified Fourier source geometry. There are 32 magnetic
cells and 63 electric amplitudes, of which 32 carry physical ionic pairs.
This is an ideal impressed source grating, not a passive material corrugation.
The incident normal channel has spatial amplitude one; a patterned transducer
multiplies it by cos(G x). Unit forcing is normalized in the second-order
magnetic equation. Coupler efficiency and open-boundary flux are not modeled. -/
noncomputable def reciprocalMomentum : ℝ := Real.sqrt 6
noncomputable def period : ℝ := 2 * Real.pi / reciprocalMomentum
noncomputable def incidentChannel (_x : ℝ) : ℝ := 1
noncomputable def sheetSource (x : ℝ) : ℝ :=
  incidentChannel x * Real.cos (reciprocalMomentum * x)
def drivenMagneticCell : Fin 32 := 15
def physicalPairCount : ℕ := 32
def physicalIonCount : ℕ := 2 * physicalPairCount

theorem source_is_periodic (x : ℝ) : sheetSource (x + period) = sheetSource x := by
  have hk : reciprocalMomentum ≠ 0 := by unfold reciprocalMomentum; positivity
  have h : reciprocalMomentum * (x + period) = reciprocalMomentum*x + 2*Real.pi := by
    unfold period
    field_simp
  simp only [sheetSource, incidentChannel, one_mul, h, Real.cos_add_two_pi]

theorem source_has_nonzero_matched_component : sheetSource 0 = 1 := by
  simp [sheetSource, incidentChannel]

end VerifiedPhysics.GratingExperiment
