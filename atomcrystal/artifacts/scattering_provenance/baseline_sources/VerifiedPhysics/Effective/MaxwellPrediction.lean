import VerifiedPhysics.Effective.TMFields

/-! This module contains the frozen higher-level prediction. Its import
closure contains no finite Maxwell slab, surface certificate, or numerical
output. The final comparison theorem is intentionally in a different module.
-/

namespace VerifiedPhysics

def maxwellPredictedSquaredFrequency : ℝ := 3
def maxwellPredictedWaveNumberSquared : ℝ := 6
noncomputable def maxwellPredictedSquaredTolerance : ℝ := 3/100

theorem frozen_maxwell_prediction :
    EffectiveSurfaceMode maxwellPredictedSquaredFrequency maxwellPredictedWaveNumberSquared :=
  predicted_surface_mode

theorem frozen_maxwell_prediction_fields :
    ∃ av am : ℝ, 0 < av ∧ 0 < am ∧
      TMRegion 1 3 6 (tmMagnetic (-av)) (tmTangential 1 (-av)) (tmNormal 1 (-av)) ∧
      TMRegion (dielectric 3) 3 6 (tmMagnetic am)
        (tmTangential (dielectric 3) am) (tmNormal (dielectric 3) am) ∧
      tmMagnetic (-av) 0 = tmMagnetic am 0 ∧
      tmTangential 1 (-av) 0 = tmTangential (dielectric 3) am 0 := by
  exact effective_mode_has_maxwell_fields 3 6 predicted_surface_mode
    (by rw [dielectric_at_prediction]; norm_num)

end VerifiedPhysics
