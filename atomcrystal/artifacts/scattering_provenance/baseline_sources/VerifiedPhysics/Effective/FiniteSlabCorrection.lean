import VerifiedPhysics.Experiments.SlabMode

namespace VerifiedPhysics

/-!
This is the first refinement after the failed planar-half-space prediction.
The two-layer termination is retained as an explicit finite-size correction.
The higher-level formula below contains no individual ionic coordinates.
`corrected_mode_from_lower_level` is the required proof that it is a law of
the declared lower-level slab operator, for every positive `k2`.
-/

noncomputable def correctedFiniteSlabFrequency (k2 : ℝ) : ℝ :=
  2 + k2 * (5 - Real.sqrt 17) / 12

def CorrectedFiniteSlabMode (s k2 : ℝ) : Prop :=
  0 < k2 ∧ s = correctedFiniteSlabFrequency k2

theorem corrected_mode_from_lower_level (k2 : ℝ) (_hk : 0 < k2) :
    AtomisticSurfaceMode (correctedFiniteSlabFrequency k2)
      k2 2 observedSurfaceAmplitude := by
  have hr2 : (Real.sqrt 17) ^ 2 = 17 :=
    Real.sq_sqrt (by norm_num)
  have hmul := congrArg (fun z : ℝ => k2 * z) hr2
  dsimp [AtomisticSurfaceMode, correctedFiniteSlabFrequency,
    observedSurfaceAmplitude, slabOperator0, slabOperator1]
  constructor
  · ring
  constructor
  · nlinarith [hmul]
  · positivity

theorem corrected_mode_localized :
    SurfaceLocalized 2 observedSurfaceAmplitude :=
  certified_slab_localization

/-- A new wave number not used in the initial interface/slab comparison. -/
theorem refined_prediction_at_withheld_wavevector :
    CorrectedFiniteSlabMode (7 - Real.sqrt 17) 12 := by
  constructor
  · norm_num
  · unfold correctedFiniteSlabFrequency
    ring

theorem refined_prediction_interval :
    (287 / 100 : ℝ) < correctedFiniteSlabFrequency 12 ∧
      correctedFiniteSlabFrequency 12 < (288 / 100 : ℝ) := by
  have hr2 : (Real.sqrt 17) ^ 2 = 17 :=
    Real.sq_sqrt (by norm_num)
  have hrn : 0 ≤ Real.sqrt 17 := Real.sqrt_nonneg _
  have hrlo : (103 / 25 : ℝ) < Real.sqrt 17 := by nlinarith [hr2]
  have hrhi : Real.sqrt 17 < (413 / 100 : ℝ) := by nlinarith [hr2]
  unfold correctedFiniteSlabFrequency
  constructor <;> nlinarith

end VerifiedPhysics
