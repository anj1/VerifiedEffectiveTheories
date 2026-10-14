import VerifiedPhysics.Atomistic.ForceBridge
import VerifiedPhysics.Experiments.WithheldSlab

namespace VerifiedPhysics

/-- A scaled version of the independently certified `k² = 12` slab mode.
At this nonzero amplitude, the full nonlinear ionic potential has a
deterministic force-equation residual bounded by `2C/125` in each layer.
This is a force residual, not an eigenfrequency or trajectory error. -/
theorem withheld_nonlinear_surface_force_residual :
    let s := 7 - Real.sqrt 17
    let u0 : ℝ := 1 / 50
    let u1 : ℝ := observedSurfaceAmplitude / 100
    0 < u0 ^ 2 + u1 ^ 2 ∧
    SurfaceLocalized u0 u1 ∧
    |deriv (fun y => nonlinearSlabPotential 12 y u1) u0 -
      reducedMass * s * u0| ≤ (2 / 125 : ℝ) * coulombMagnitude ∧
    |deriv (fun y => nonlinearSlabPotential 12 u0 y) u1 -
      reducedMass * s * u1| ≤ (2 / 125 : ℝ) * coulombMagnitude := by
  dsimp only
  have hsqrt : (Real.sqrt 17) ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  have hsqrt_nonneg : 0 ≤ Real.sqrt 17 := Real.sqrt_nonneg _
  have hsqrt_lt : Real.sqrt 17 < (5 : ℝ) := by nlinarith
  have hamp : |observedSurfaceAmplitude| ≤ (2 : ℝ) := by
    dsimp [observedSurfaceAmplitude]
    rw [abs_le]
    constructor <;> nlinarith
  have hu0 : |(1 / 50 : ℝ)| ≤ (1 / 2 : ℝ) := by norm_num
  have hu1small : |observedSurfaceAmplitude / 100| ≤ (1 / 50 : ℝ) := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 100)]
    exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 100)).2 (by nlinarith)
  have hu1 : |observedSurfaceAmplitude / 100| ≤ (1 / 2 : ℝ) := by
    linarith
  have hs0 : slabOperator0 12 (1 / 50) (observedSurfaceAmplitude / 100) =
      (7 - Real.sqrt 17) * (1 / 50) := by
    calc
      slabOperator0 12 (1 / 50) (observedSurfaceAmplitude / 100) =
          (1 / 100 : ℝ) * slabOperator0 12 2 observedSurfaceAmplitude := by
            dsimp [slabOperator0]; ring
      _ = (7 - Real.sqrt 17) * (1 / 50) := by
        rw [withheld_slab_eigenpair.1]
        ring
  have hs1 : slabOperator1 12 (1 / 50) (observedSurfaceAmplitude / 100) =
      (7 - Real.sqrt 17) * (observedSurfaceAmplitude / 100) := by
    calc
      slabOperator1 12 (1 / 50) (observedSurfaceAmplitude / 100) =
          (1 / 100 : ℝ) * slabOperator1 12 2 observedSurfaceAmplitude := by
            dsimp [slabOperator1]; ring
      _ = (7 - Real.sqrt 17) * (observedSurfaceAmplitude / 100) := by
        rw [withheld_slab_eigenpair.2.1]
        ring
  have hb := nonlinear_to_harmonic_surface_bound 12
    (1 / 50) (observedSurfaceAmplitude / 100) hu0 hu1
  have hC : 0 ≤ coulombMagnitude := le_of_lt coulomb_magnitude_positive
  refine ⟨by positivity, ?_, ?_, ?_⟩
  · have h := certified_slab_localization
    dsimp [SurfaceLocalized] at h ⊢
    nlinarith
  · have heq : reducedMass * (7 - Real.sqrt 17) * (1 / 50) =
        reducedMass * slabOperator0 12 (1 / 50)
          (observedSurfaceAmplitude / 100) := by rw [hs0]; ring
    rw [heq]
    calc
      _ ≤ 40 * coulombMagnitude * |(1 / 50 : ℝ)| ^ 2 := hb.1
      _ = (2 / 125 : ℝ) * coulombMagnitude := by norm_num; ring
  · have heq : reducedMass * (7 - Real.sqrt 17) *
        (observedSurfaceAmplitude / 100) =
        reducedMass * slabOperator1 12 (1 / 50)
          (observedSurfaceAmplitude / 100) := by rw [hs1]; ring
    rw [heq]
    calc
      _ ≤ 40 * coulombMagnitude * |observedSurfaceAmplitude / 100| ^ 2 := hb.2
      _ ≤ (2 / 125 : ℝ) * coulombMagnitude := by
        have hsq : |observedSurfaceAmplitude / 100| ^ 2 ≤ (1 / 50 : ℝ) ^ 2 := by
          gcongr
        nlinarith

end VerifiedPhysics
