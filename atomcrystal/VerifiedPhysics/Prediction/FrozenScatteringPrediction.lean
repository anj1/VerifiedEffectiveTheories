import VerifiedPhysics.Prediction.GratingDesign
import VerifiedPhysics.Effective.MaxwellPrediction

/-! Frozen before any driven microscopic solve. A hypothesis is data, not a
proof of its later validation. No experiment or certificate is imported.

The continuum TM pole at s=3 motivates testing unit-source interface magnetic
intensity at s=3 against s=4. The conservative, falsifiable hypothesis is an
intensity at least one and at least four times the control intensity. No
continuum theorem asserts these finite-box amplitude thresholds.
-/
namespace VerifiedPhysics.ScatteringPrediction

def driveSquaredFrequency : ℝ := 3
def controlSquaredFrequency : ℝ := 4
noncomputable def predictedSquaredInterval : Set ℝ := Set.Icc (297/100) (303/100)
def minimumIntensity : ℝ := 1
def minimumContrast : ℝ := 4

/-- Distinct budgets: exact bulk/continuum theory at zero bias; finite-model
frequency allowance; exact ideal momentum conversion; exact arithmetic. -/
def bulkError : ℝ := 0
def continuumError : ℝ := 0
noncomputable def finiteSlabSquaredAllowance : ℝ := 3/100
def momentumError : ℝ := 0
def numericalError : ℝ := 0

theorem frozen_effective_prediction :
    EffectiveSurfaceMode driveSquaredFrequency 6 ∧
    driveSquaredFrequency ∈ predictedSquaredInterval ∧
    controlSquaredFrequency ∉ predictedSquaredInterval := by
  refine ⟨predicted_surface_mode, ?_, ?_⟩ <;>
    norm_num [driveSquaredFrequency, controlSquaredFrequency, predictedSquaredInterval]

theorem budget_interval_containment (s : ℝ)
    (h : |s - driveSquaredFrequency| ≤ bulkError + continuumError +
      finiteSlabSquaredAllowance + numericalError) :
    s ∈ predictedSquaredInterval := by
  change |s - 3| ≤ (0:ℝ) + 0 + 3/100 + 0 at h
  change 297/100 ≤ s ∧ s ≤ 303/100
  constructor <;> linarith [(abs_le.mp h).1, (abs_le.mp h).2]

end VerifiedPhysics.ScatteringPrediction
