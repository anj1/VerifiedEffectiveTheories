import VerifiedPhysics.Effective.GratingProposal

namespace VerifiedPhysics.ScatteringPrediction

noncomputable def vacuumParallelMomentum (θ ω : ℝ) : ℝ := ω * Real.sin θ

/-- Every propagating vacuum incidence angle fails, throughout the frozen
squared-frequency window, not just at normal incidence. -/
theorem direct_incidence_cannot_match (θ s : ℝ)
    (hs : s ∈ Set.Icc (297/100 : ℝ) (303/100)) :
    vacuumParallelMomentum θ (Real.sqrt s) < Real.sqrt 6 := by
  have h : Real.sqrt s < Real.sqrt 6 :=
    Real.sqrt_lt_sqrt (by linarith [hs.1]) (by linarith [hs.2])
  have hsin := Real.sin_le_one θ
  unfold vacuumParallelMomentum
  nlinarith [Real.sqrt_nonneg s]

end VerifiedPhysics.ScatteringPrediction
