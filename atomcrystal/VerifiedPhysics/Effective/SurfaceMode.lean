import VerifiedPhysics.Bulk.DielectricLaw

namespace VerifiedPhysics

/-- The negative-permittivity (lossless Reststrahlen) interval of this model. -/
theorem reststrahlen_negative {s : ℝ} (hs : 2 < s) (ht : s < 5) :
    dielectric s < 0 := by
  unfold dielectric
  apply div_neg_of_pos_of_neg
  · linarith
  · linarith

/-- A planar TM surface solution specified by positive evanescence rates
on the vacuum and material sides. The two square equations are the two bulk
Maxwell wave equations; the last is the tangential boundary condition.
`k2` is the square of the in-plane wave number. -/
def EffectiveSurfaceMode (s k2 : ℝ) : Prop :=
  ∃ aVac aMat : ℝ,
    0 < aVac ∧ 0 < aMat ∧
    aVac ^ 2 = k2 - s ∧
    aMat ^ 2 = k2 - dielectric s * s ∧
    dielectric s * aVac + aMat = 0

/-- The familiar TM dispersion is a consequence of the wave and boundary
equations, rather than the definition of a surface mode. -/
theorem effective_surface_dispersion {s k2 : ℝ}
    (hmode : EffectiveSurfaceMode s k2)
    (he : dielectric s ≠ 1) :
    k2 * (1 + dielectric s) = s * dielectric s := by
  rcases hmode with ⟨aVac, aMat, _, _, hv, hm, hb⟩
  have hsq : dielectric s ^ 2 * (k2 - s) =
      k2 - dielectric s * s := by
    calc
      _ = (dielectric s * aVac) ^ 2 := by rw [← hv]; ring
      _ = aMat ^ 2 := by
        have ha : aMat = -(dielectric s * aVac) := by linarith
        rw [ha]
        ring
      _ = _ := hm
  have hfactor : (dielectric s - 1) *
      (k2 * (1 + dielectric s) - s * dielectric s) = 0 := by
    nlinarith [hsq]
  have hzero := (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr he)
  linarith

theorem dielectric_at_prediction : dielectric 3 = -2 := by
  norm_num [dielectric]

/-- The effective theory predicts this squared frequency and wave number
before the slab operator is inspected. -/
theorem predicted_surface_mode : EffectiveSurfaceMode 3 6 := by
  refine ⟨Real.sqrt 3, 2 * Real.sqrt 3, ?_, ?_, ?_, ?_, ?_⟩
  · exact Real.sqrt_pos.2 (by norm_num)
  · have h : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
    positivity
  · norm_num [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  · rw [dielectric_at_prediction]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  · rw [dielectric_at_prediction]
    ring

theorem predicted_outside_light_cone : (3 : ℝ) < 6 := by
  norm_num

end VerifiedPhysics
