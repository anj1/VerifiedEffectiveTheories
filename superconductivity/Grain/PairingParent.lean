import Grain.HarmonicBand
import Grain.PairingMaterial
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Harmonic exchange and the exact Cooper matrix elements available from
the finite real, spin-degenerate parent. The frequency calculation uses
the quadratic imaginary-time action at each Fourier component. -/

namespace Grain.Pairing.Material

open HarmonicBand

variable {n c m : ℕ}

/-- A normalized oscillator vertex built from the mass-weighted derivative. -/
noncomputable def parentMode (d : HarmonicBand.Input n c m) (i j : Orbital n)
    (k : Fin m) : RealMode :=
  ⟨frequency d k, ((modeEntry d k i j : ℝ) * coupling d k)^2⟩

theorem parent_mode_response (d : HarmonicBand.Input n c m) (h : Valid d)
    (i j : Orbital n) (k : Fin m) (q : ℝ) :
    modeResponse (parentMode d i j k) q = (modeEntry d k i j : ℝ)^2 / (d.force k + q) := by
  have hp := frequency_pos d h k
  have hf : 0 < (d.force k : ℝ) := by exact_mod_cast (h.2.2.2.2.1 k).1
  have hs : frequency d k * frequency d k = (d.force k : ℝ) := Real.mul_self_sqrt hf.le
  unfold modeResponse parentMode
  dsimp only
  rw [hs, coupling, mul_pow, div_pow, one_pow, Real.sq_sqrt (by positivity)]
  congr 1
  field_simp

/-- The quadratic action of one real Fourier component with two real
sources. The mixed term after the shift is the exchange; the source
squares are the two self terms. -/
theorem harmonic_fourier_shift (d : HarmonicBand.Input n c m) (h : Valid d)
    (i j : Orbital n) (k : Fin m) (ν u x y : ℝ) :
    let K := (d.force k : ℝ) + ν^2
    let g := (modeEntry d k i j : ℝ)
    K / 2 * u^2 + g * (x + y) * u =
      K / 2 * (u + g * (x + y) / K)^2 -
      g^2 / (2 * K) * (x^2 + y^2) - modeResponse (parentMode d i j k) (ν^2) * x * y := by
  dsimp only
  rw [parent_mode_response d h]
  have hf : 0 < (d.force k : ℝ) := by exact_mod_cast (h.2.2.2.2.1 k).1
  have hk : (d.force k : ℝ) + ν^2 ≠ 0 := by positivity
  field_simp
  ring

/-- Integrating out the shifted Fourier coordinate leaves the free
Gaussian integral times the exponential of the induced source term. -/
theorem harmonic_fourier_integral (d : HarmonicBand.Input n c m) (h : Valid d)
    (i j : Orbital n) (k : Fin m) (ν x y : ℝ) :
    let K := (d.force k : ℝ) + ν^2
    let g := (modeEntry d k i j : ℝ)
    (∫ u : ℝ, Real.exp (-(K / 2 * u^2 + g * (x + y) * u))) =
      Real.exp (g^2 / (2 * K) * (x^2 + y^2) + modeResponse (parentMode d i j k) (ν^2) * x * y) *
        (∫ u : ℝ, Real.exp (-(K / 2 * u^2))) := by
  let K := (d.force k : ℝ) + ν^2
  let g := (modeEntry d k i j : ℝ)
  let c := g * (x + y) / K
  let E := g^2 / (2 * K) * (x^2 + y^2) + modeResponse (parentMode d i j k) (ν^2) * x * y
  change (∫ u : ℝ, Real.exp (-(K / 2 * u^2 + g * (x + y) * u))) = _
  calc
    _ = ∫ u : ℝ, Real.exp E * Real.exp (-(K / 2 * (u + c)^2)) := by
      congr 1
      funext u
      rw [← Real.exp_add]
      congr 1
      have hh := harmonic_fourier_shift d h i j k ν u x y
      change K / 2 * u^2 + g * (x + y) * u = K / 2 * (u + c)^2 - _ - _ at hh
      dsimp [E]
      linarith only [hh]
    _ = _ := by
      rw [MeasureTheory.integral_const_mul]
      congr 1
      exact (MeasureTheory.measurePreserving_add_right MeasureTheory.volume c).integral_comp
        (MeasurableEquiv.addRight c).measurableEmbedding (fun u => Real.exp (-(K / 2 * u^2)))

/-- The signed radial normal-propagator integral for a constant DOS on a
symmetric band of half-width W, with the DOS factored out. -/
noncomputable def normalBandFactor (ω W : ℝ) : ℝ :=
  ∫ ξ : ℝ in -W..W, ω / (ω^2 + ξ^2)

theorem normal_band_factor (ω W : ℝ) :
    normalBandFactor ω W = 2 * Real.arctan (W / ω) := by
  unfold normalBandFactor
  rw [integral_div_sq_add_sq, neg_div, Real.arctan_neg]
  ring

/-- The infinite-width normal projection uses π at positive frequency.
The finite-band correction tends to zero as the band is widened. -/
theorem normal_band_error {ω W : ℝ} (hω : 0 < ω) (hW : 0 < W) :
    0 ≤ Real.pi - normalBandFactor ω W ∧
      Real.pi - normalBandFactor ω W ≤ 2 * ω / W := by
  have hp := div_pos hω hW
  have he : Real.pi - normalBandFactor ω W = 2 * Real.arctan (ω / W) := by
    rw [normal_band_factor, ← inv_div, Real.arctan_inv_of_pos hp]
    ring
  rw [he, mul_div_assoc]
  exact ⟨mul_nonneg (by norm_num) (Real.arctan_nonneg.mpr (div_nonneg hω.le hW.le)),
    mul_le_mul_of_nonneg_left (Real.arctan_le_self (div_nonneg hω.le hW.le)) (by norm_num)⟩

/-- Occupation state of an up/down pair in a real spin-degenerate orbital. -/
def pairState (i : Orbital n) : State n :=
  Fin.ofNat _ (2 ^ slot (i, 0) + 2 ^ slot (i, 1))

/-- Projection of the parent's screened operator onto the stated pair basis.
The screening convention is inherited from the parent input. -/
def parentCoulomb (d : HarmonicBand.Input n c m) (i j : Orbital n) : ℚ :=
  screened d (pairState i) (pairState j)

/-- Orbital-resolved export before any patch averaging. Bands here are
measured from the supplied chemical potential. -/
noncomputable def parentRealization (d : HarmonicBand.Input n c m) (μ : ℝ) :
    Realization (Orbital n) where
  bands i := [(d.levels i : ℝ) - μ]
  modes i j := (List.ofFn fun k => parentMode d i j k)
  coulomb i j := parentCoulomb d i j

theorem parent_phonon (d : HarmonicBand.Input n c m) (h : Valid d)
    (μ q : ℝ) (i j : Orbital n) :
    phononResponse ((parentRealization d μ).modes i j) q =
      ∑ k : Fin m, (modeEntry d k i j : ℝ)^2 / (d.force k + q) := by
  simp [parentRealization, phononResponse, List.map_ofFn, List.sum_ofFn, parent_mode_response d h]

end Grain.Pairing.Material
