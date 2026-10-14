import VerifiedPhysics.Effective.SurfaceMode

namespace VerifiedPhysics

/-- Real and imaginary parts of the reflection amplitude obtained by
matching an incoming unit-amplitude vacuum wave to a decaying material wave. -/
noncomputable def reflectionReal (k a : ℝ) : ℝ := (k^2-a^2)/(k^2+a^2)
noncomputable def reflectionImag (k a : ℝ) : ℝ := -2*k*a/(k^2+a^2)

theorem evanescent_reflection_boundary (k a : ℝ) (hk : 0 < k) (ha : 0 < a) :
    k * reflectionImag k a = -a*(1+reflectionReal k a) ∧
    k * (1-reflectionReal k a) = -a*reflectionImag k a ∧
    reflectionReal k a ^ 2 + reflectionImag k a ^ 2 = 1 := by
  have hd : k^2+a^2 ≠ 0 := by positivity
  unfold reflectionReal reflectionImag
  constructor
  · field_simp [hd]; ring
  constructor <;> field_simp [hd] <;> ring

/-- Lossless Reststrahlen reflection in the effective Maxwell half-space:
negative dielectric response gives an evanescent transmitted field and unit
reflected intensity. This is a theorem of the effective infinite half-space,
distinct from the finite surface-mode test. -/
theorem reststrahlen_unit_reflectivity (s : ℝ) (hs : 2 < s) (ht : s < 5) :
    ∃ a : ℝ, 0 < a ∧ a^2 = -dielectric s*s ∧
      reflectionReal (Real.sqrt s) a ^ 2 + reflectionImag (Real.sqrt s) a ^ 2 = 1 := by
  have he : dielectric s < 0 := reststrahlen_negative hs ht
  have hprod : 0 < -dielectric s*s := mul_pos (neg_pos.mpr he) (by linarith)
  refine ⟨Real.sqrt (-dielectric s*s), Real.sqrt_pos.mpr hprod,
    Real.sq_sqrt (le_of_lt hprod), ?_⟩
  exact (evanescent_reflection_boundary _ _
    (Real.sqrt_pos.mpr (by linarith)) (Real.sqrt_pos.mpr hprod)).2.2

end VerifiedPhysics
