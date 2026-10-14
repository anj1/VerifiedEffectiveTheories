import VerifiedPhysics.Effective.SurfaceMode

namespace VerifiedPhysics

noncomputable def tmMagnetic (rate z : ℝ) : ℝ := Real.exp (rate*z)
noncomputable def tmTangential (e rate z : ℝ) : ℝ := (rate/e)*Real.exp (rate*z)
noncomputable def tmNormal (e rate z : ℝ) : ℝ := Real.exp (rate*z)/e

/-- Source-free TM Maxwell equations in real Fourier quadratures. The normal
electric amplitude is divided by `k`, and the tangential amplitude includes
the usual phase factor. `e` is the sole material input. -/
def TMRegion (e s k2 : ℝ) (H T N : ℝ → ℝ) : Prop :=
  ∀ z : ℝ, deriv H z = e*T z ∧ e*N z = H z ∧
    deriv T z = k2*N z-s*H z

theorem tm_exponential_derivative (rate z : ℝ) :
    deriv (tmMagnetic rate) z = rate * Real.exp (rate*z) := by
  have h : HasDerivAt (tmMagnetic rate) (rate*Real.exp (rate*z)) z := by
    convert (Real.hasDerivAt_exp (rate*z)).comp z ((hasDerivAt_id z).const_mul rate) using 1
    · funext y; rfl
    · ring
  exact h.deriv

theorem tm_region_from_dispersion (e s k2 rate : ℝ) (he : e ≠ 0)
    (hr : rate^2 = k2-e*s) :
    TMRegion e s k2 (tmMagnetic rate) (tmTangential e rate) (tmNormal e rate) := by
  intro z
  refine ⟨?_, ?_, ?_⟩
  · rw [tm_exponential_derivative]
    dsimp [tmTangential]
    field_simp [he]
  · dsimp [tmNormal, tmMagnetic]
    field_simp [he]
  · have hd : deriv (tmTangential e rate) z = (rate/e) * (rate * Real.exp (rate*z)) := by
      unfold tmTangential
      rw [deriv_const_mul_field]
      exact congrArg (fun t : ℝ => (rate/e)*t) (tm_exponential_derivative rate z)
    rw [hd]
    dsimp [tmNormal, tmMagnetic]
    field_simp [he]
    nlinarith [congrArg (fun t : ℝ => t * Real.exp (rate*z)) hr]

/-- Explicit decaying Maxwell fields and tangential interface continuity.
The material field decays for `z ≤ 0`, the vacuum field for `z ≥ 0`. -/
theorem effective_mode_has_maxwell_fields (s k2 : ℝ)
    (h : EffectiveSurfaceMode s k2) (he : dielectric s ≠ 0) :
    ∃ av am : ℝ, 0 < av ∧ 0 < am ∧
      TMRegion 1 s k2 (tmMagnetic (-av)) (tmTangential 1 (-av)) (tmNormal 1 (-av)) ∧
      TMRegion (dielectric s) s k2 (tmMagnetic am)
        (tmTangential (dielectric s) am) (tmNormal (dielectric s) am) ∧
      tmMagnetic (-av) 0 = tmMagnetic am 0 ∧
      tmTangential 1 (-av) 0 = tmTangential (dielectric s) am 0 := by
  obtain ⟨av, am, hv, hm, hvs, hms, hboundary⟩ := h
  refine ⟨av, am, hv, hm, ?_, ?_, ?_, ?_⟩
  · apply tm_region_from_dispersion _ _ _ _ (by norm_num)
    nlinarith
  · exact tm_region_from_dispersion _ _ _ _ he hms
  · simp [tmMagnetic]
  · simp only [tmTangential, mul_zero, Real.exp_zero, mul_one, div_one]
    apply (eq_div_iff he).2
    nlinarith

end VerifiedPhysics
