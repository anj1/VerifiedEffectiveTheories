import VerifiedPhysics.Experiments.SlabMode

namespace VerifiedPhysics

/-!
This certificate imports only the lower-level slab operator, not the
corrected effective theory. Its proof is checked at `k2 = 12`, withheld
from the original `k2 = 6` surface test. This import separation makes the
formal dependency independent, though chronological provenance still needs
the accompanying frozen artifacts.
-/

theorem withheld_slab_operator (x0 x1 : ℝ) :
    slabOperator0 12 x0 x1 = 6 * x0 - 4 * x1 ∧
    slabOperator1 12 x0 x1 = -4 * x0 + 8 * x1 := by
  constructor <;> norm_num [slabOperator0, slabOperator1]

theorem withheld_characteristic_signs :
    (287 / 100 : ℝ) ^ 2 - 14 * (287 / 100 : ℝ) + 32 = 569 / 10000 ∧
    (288 / 100 : ℝ) ^ 2 - 14 * (288 / 100 : ℝ) + 32 = -16 / 625 := by
  constructor <;> norm_num

theorem withheld_slab_eigenpair :
    AtomisticSurfaceMode (7 - Real.sqrt 17) 12 2
      observedSurfaceAmplitude := by
  have hr2 : (Real.sqrt 17) ^ 2 = 17 :=
    Real.sq_sqrt (by norm_num)
  dsimp [AtomisticSurfaceMode, observedSurfaceAmplitude]
  constructor
  · rw [(withheld_slab_operator _ _).1]
    nlinarith [hr2]
  constructor
  · rw [(withheld_slab_operator _ _).2]
    nlinarith [hr2]
  · positivity

end VerifiedPhysics
