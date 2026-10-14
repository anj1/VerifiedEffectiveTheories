import VerifiedPhysics.Effective.SurfaceMode

namespace VerifiedPhysics

/-!
The lower-level slab is independently specified by two relative ionic
coordinates. Its transverse-field energy is a finite electrostatic model:

  U = 3(x₀²+x₁²) + (k²/2)(x₀-x₁)² + (k²/4)x₁².

The last term is the declared terminating boundary condition. The ions have
the same reduced mass three as the bulk pair. This is an exact two-layer
model, not an atomistic Maxwell scattering calculation or a real NaCl slab.
-/

noncomputable def slabPotential (k2 x0 x1 : ℝ) : ℝ :=
  3 * (x0 ^ 2 + x1 ^ 2) +
  (k2 / 2) * (x0 - x1) ^ 2 + (k2 / 4) * x1 ^ 2

noncomputable def slabKinetic (v0 v1 : ℝ) : ℝ :=
  (reducedMass / 2) * (v0 ^ 2 + v1 ^ 2)

/-- The explicit mass-normalized Hessian of `slabPotential`. -/
noncomputable def slabOperator0 (k2 x0 x1 : ℝ) : ℝ :=
  (2 + k2 / 3) * x0 - (k2 / 3) * x1

noncomputable def slabOperator1 (k2 x0 x1 : ℝ) : ℝ :=
  -(k2 / 3) * x0 + (2 + k2 / 2) * x1

theorem slab_hessian_bridge (k2 x0 x1 : ℝ) :
    deriv (fun y => slabPotential k2 y x1) x0 =
      reducedMass * slabOperator0 k2 x0 x1 ∧
    deriv (fun y => slabPotential k2 x0 y) x1 =
      reducedMass * slabOperator1 k2 x0 x1 := by
  constructor
  · have hf : (fun y : ℝ => slabPotential k2 y x1) =
        (fun y : ℝ => ((3 + k2 / 2) * y ^ 2 + (-k2 * x1) * y) +
          (3 + 3 * k2 / 4) * x1 ^ 2) := by
      funext y
      dsimp [slabPotential]
      ring
    rw [hf, deriv_add_const]
    change deriv ((fun y : ℝ => (3 + k2 / 2) * y ^ 2) +
      (fun y : ℝ => (-k2 * x1) * y)) x0 = _
    rw [deriv_add (by fun_prop) (by fun_prop)]
    rw [deriv_const_mul_field, deriv_pow_field, deriv_const_mul_id]
    dsimp [reducedMass, slabOperator0]
    ring
  · have hf : (fun y : ℝ => slabPotential k2 x0 y) =
        (fun y : ℝ => ((3 + 3 * k2 / 4) * y ^ 2 + (-k2 * x0) * y) +
          (3 + k2 / 2) * x0 ^ 2) := by
      funext y
      dsimp [slabPotential]
      ring
    rw [hf, deriv_add_const]
    change deriv ((fun y : ℝ => (3 + 3 * k2 / 4) * y ^ 2) +
      (fun y : ℝ => (-k2 * x0) * y)) x1 = _
    rw [deriv_add (by fun_prop) (by fun_prop)]
    rw [deriv_const_mul_field, deriv_pow_field, deriv_const_mul_id]
    dsimp [reducedMass, slabOperator1]
    ring

def AtomisticSurfaceMode (s k2 x0 x1 : ℝ) : Prop :=
  slabOperator0 k2 x0 x1 = s * x0 ∧
  slabOperator1 k2 x0 x1 = s * x1 ∧
  0 < x0 ^ 2 + x1 ^ 2

/-- At least three fifths of the squared ionic displacement is in the
surface layer (layer zero). -/
def SurfaceLocalized (x0 x1 : ℝ) : Prop :=
  (3 / 5 : ℝ) * (x0 ^ 2 + x1 ^ 2) ≤ x0 ^ 2

noncomputable def observedSquaredFrequency : ℝ := (9 - Real.sqrt 17) / 2
noncomputable def observedSurfaceAmplitude : ℝ := (Real.sqrt 17 - 1) / 2

private theorem sqrt17_sq : (Real.sqrt 17) ^ 2 = 17 := by
  exact Real.sq_sqrt (by norm_num)

private theorem sqrt17_lower : (4 : ℝ) < Real.sqrt 17 := by
  have hn : 0 ≤ Real.sqrt 17 := Real.sqrt_nonneg _
  nlinarith [sqrt17_sq]

private theorem sqrt17_upper : Real.sqrt 17 < (21 / 5 : ℝ) := by
  have hn : 0 ≤ Real.sqrt 17 := Real.sqrt_nonneg _
  nlinarith [sqrt17_sq]

/-- The initial zero-width effective prediction fails for this finite slab. -/
theorem predicted_eigenvalue_rejected :
    ¬ ∃ x0 x1 : ℝ, AtomisticSurfaceMode 3 6 x0 x1 := by
  rintro ⟨x0, x1, h0, h1, hpos⟩
  dsimp [AtomisticSurfaceMode, slabOperator0, slabOperator1] at h0 h1
  norm_num at h0 h1
  nlinarith [sq_nonneg x0, sq_nonneg x1]

theorem certified_slab_mode :
    AtomisticSurfaceMode observedSquaredFrequency 6 2 observedSurfaceAmplitude := by
  dsimp [AtomisticSurfaceMode, observedSquaredFrequency,
    observedSurfaceAmplitude, slabOperator0, slabOperator1]
  constructor
  · nlinarith [sqrt17_sq]
  constructor
  · nlinarith [sqrt17_sq]
  · positivity

theorem certified_slab_localization :
    SurfaceLocalized 2 observedSurfaceAmplitude := by
  dsimp [SurfaceLocalized, observedSurfaceAmplitude]
  nlinarith [sqrt17_sq, sqrt17_lower]

theorem certified_frequency_discrepancy :
    (1 / 2 : ℝ) < |observedSquaredFrequency - 3| ∧
    |observedSquaredFrequency - 3| < (3 / 5 : ℝ) := by
  dsimp [observedSquaredFrequency]
  rw [abs_sub_comm]
  rw [abs_of_pos (by linarith [sqrt17_lower])]
  constructor
  · linarith [sqrt17_lower]
  · linarith [sqrt17_upper]

end VerifiedPhysics
