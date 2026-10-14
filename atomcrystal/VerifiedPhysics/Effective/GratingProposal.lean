import VerifiedPhysics.Effective.SurfaceMode

namespace VerifiedPhysics

/-- The incidence parameter `u` is `sin θ`; physical far-field incidence has
`|u| ≤ 1`. The integer `m` is the grating diffraction order. -/
noncomputable def phaseMatching (s kParallel u G : ℝ) (m : ℤ) : Prop :=
  Real.sqrt s * u + (m : ℝ) * G = kParallel

theorem direct_far_field_cannot_match (u : ℝ) (hu : |u| ≤ 1) :
    ¬ phaseMatching 3 (Real.sqrt 6) u 0 0 := by
  intro h
  have hu' := (abs_le.mp hu).2
  have h3 : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hlt : Real.sqrt 3 < Real.sqrt 6 :=
    Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  dsimp [phaseMatching] at h
  nlinarith

/-- A normal-incidence, first-order grating proposal. Its period is chosen
from the higher-level momentum mismatch alone. -/
noncomputable def proposedGratingG : ℝ := Real.sqrt 6
noncomputable def proposedGratingPeriod : ℝ :=
  2 * Real.pi / proposedGratingG

theorem proposed_grating_period_positive : 0 < proposedGratingPeriod := by
  unfold proposedGratingPeriod proposedGratingG
  positivity

theorem proposed_grating_reciprocal_vector :
    2 * Real.pi / proposedGratingPeriod = proposedGratingG := by
  have hG : proposedGratingG ≠ 0 := by
    unfold proposedGratingG
    positivity
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  unfold proposedGratingPeriod
  field_simp

theorem proposed_grating_phase_matching :
    phaseMatching 3 (Real.sqrt 6) 0 proposedGratingG 1 := by
  simp [phaseMatching, proposedGratingG]

end VerifiedPhysics
