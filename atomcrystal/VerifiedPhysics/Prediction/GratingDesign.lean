import VerifiedPhysics.Prediction.SurfaceMomentum

namespace VerifiedPhysics.ScatteringPrediction

/-- Deterministic design rule: normal incidence, smallest positive diffraction
order, reciprocal momentum equal to the predicted surface momentum. -/
def selectedAngle : ℝ := 0
def selectedOrder : ℤ := 1
noncomputable def selectedPeriod : ℝ := proposedGratingPeriod

theorem selected_grating_matches (ω : ℝ) :
    0 < selectedPeriod ∧
    |vacuumParallelMomentum selectedAngle ω +
      (selectedOrder : ℝ) * (2 * Real.pi / selectedPeriod) - Real.sqrt 6| ≤ 0 := by
  refine ⟨proposed_grating_period_positive, ?_⟩
  simp [vacuumParallelMomentum, selectedAngle, selectedOrder, selectedPeriod,
    proposed_grating_reciprocal_vector, proposedGratingG]

end VerifiedPhysics.ScatteringPrediction
