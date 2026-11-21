import Grain.PhononVariational
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Bounds for comparing retained and primitive quadratic forms and
propagating finite-temperature free-energy enclosures. -/

namespace Grain.EFT

open Phonon
open scoped BigOperators

/-- Completing the square bounds the effect of a residual in the discarded rows. -/
theorem residual_penalty {q : Type} [Fintype q] (r y : q → ℝ)
    {δ : ℝ} (hδ : 0 < δ) :
    -(normSq r / δ) ≤ δ * normSq y + 2 * Phonon.inner y r := by
  unfold normSq Phonon.inner
  rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div, ← Finset.sum_neg_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  apply (mul_le_mul_iff_left₀ hδ).mp
  have h : -(r i ^ 2 / δ) * δ = -(r i ^ 2) := by field_simp
  rw [h]
  nlinarith [sq_nonneg (δ * y i + r i)]

/-- The lifted form is an upper bound on the infimum over discarded
coordinates. A positive pivot lower bound makes the squared residual
an upper bound on the loss from an inexact lift. -/
theorem lifted_enclosure {p q : Type} [Fintype p] [Fintype q]
    (full : (p → ℝ) → (q → ℝ) → ℝ)
    (lift residual : (p → ℝ) → (q → ℝ))
    (tail : (q → ℝ) → ℝ) {δ ε : ℝ}
    (hδ : 0 < δ)
    (hgap : ∀ y, δ * normSq y ≤ tail y)
    (hexpand : ∀ x y, full x (lift x + y) =
      full x (lift x) + 2 * Phonon.inner y (residual x) + tail y)
    (herror : ∀ x, normSq (residual x) ≤ δ * ε * normSq x)
    (x : p → ℝ) :
    (∀ y, full x (lift x) - ε * normSq x ≤ full x y) ∧
    (∃ y, full x y ≤ full x (lift x)) := by
  constructor
  · intro y
    have hwrite : lift x + (y - lift x) = y := by abel
    have h := hexpand x (y - lift x)
    rw [hwrite] at h
    have hr := residual_penalty (residual x) (y - lift x) hδ
    have he : normSq (residual x) / δ ≤ ε * normSq x :=
      (div_le_iff₀ hδ).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using herror x)
    linarith [hgap (y - lift x)]
  · exact ⟨lift x, le_rfl⟩

/-- The Frobenius norm controls every residual vector produced by a matrix. -/
theorem frobenius_residual {p q : Type} [Fintype p] [Fintype q]
    (r : q → p → ℝ) (x : p → ℝ) :
    normSq (fun i => ∑ j, r i j * x j) ≤
      (∑ i, ∑ j, r i j ^ 2) * normSq x := by
  unfold normSq
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ =>
    Finset.sum_mul_sq_le_sq_mul_sq _ (r i) x

/-- Pairing-channel mean field is obtained by removing the explicitly
displayed square. Both the coupling to the pair field and its constant
are fixed by the original interaction. -/
theorem pairing_square {e : Type} [Fintype e] (x pair : e → ℝ)
    {g : ℝ} (hg : g ≠ 0) (Δ : ℝ) :
    -g * normSq pair =
      -2 * Δ * Phonon.inner pair x + Δ^2 / g * normSq x -
        g * normSq (fun i => pair i - Δ / g * x i) := by
  have hs := complete_square x pair (-(Δ / g))
  simp only [neg_mul, ← sub_eq_add_neg] at hs
  rw [hs]
  field_simp
  ring

/-- Completing all harmonic squares with mode-specific frequencies. The
annihilated amplitudes may range over any phonon occupation box. -/
theorem mode_squares {e m : Type} [Fintype e] [Fintype m]
    (ω α : m → ℝ) (vertices lowered : m → e → ℝ) :
    (∑ j, (ω j * normSq (lowered j) +
      2 * ω j * α j * Phonon.inner (lowered j) (vertices j))) =
    -(∑ j, ω j * (α j)^2 * normSq (vertices j)) +
      ∑ j, ω j * normSq (fun i => lowered j i + α j * vertices j i) := by
  rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [complete_square]
  ring

/-- The electronic term induced by a mass-weighted potential derivative.
The displacement amplitude of that derivative is `1 / √(2 ω³)`. -/
theorem dfpt_induced_coefficient {ω : ℝ} (h : 0 < ω) :
    ω * (1 / Real.sqrt (2 * ω^3))^2 = 1 / (2 * ω^2) := by
  rw [div_pow, one_pow, Real.sq_sqrt (by positivity)]
  field_simp

/-- A displaced electronic comparison is a lower bound at every phonon
occupation. No cardinality bound on the oscillator space enters this step. -/
theorem mode_lower {e m p : Type} [Fintype e] [Fintype m] [Fintype p]
    (K : (e → ℝ) → ℝ) (A : m → (e → ℝ) → (e → ℝ))
    (ω α : m → ℝ) (hω : ∀ j, 0 ≤ ω j) (l : ℝ)
    (hl : ∀ x, l * normSq x ≤ K x - ∑ j, ω j * (α j)^2 * normSq (A j x))
    (ψ : p → e → ℝ) (lowered : m → p → e → ℝ) :
    l * (∑ q, normSq (ψ q)) ≤
      ∑ q, (K (ψ q) + ∑ j, (ω j * normSq (lowered j q) +
        2 * ω j * α j * Phonon.inner (lowered j q) (A j (ψ q)))) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q _
  rw [mode_squares]
  have hs : 0 ≤ ∑ j, ω j * normSq (fun i => lowered j q i + α j * A j (ψ q) i) :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hω j) (normSq_nonneg _)
  linarith [hl (ψ q)]

/-- The vacuum plus one-quantum trial uses the actual energy of each
dressed component. The cost may either be evaluated or bounded uniformly. -/
theorem mode_dressed_upper {e m : Type} [Fintype e] [Fintype m]
    (K : (e → ℝ) → ℝ) (A : m → (e → ℝ) → (e → ℝ))
    (ω α : m → ℝ) (x : e → ℝ) {u ε : ℝ} (hε : 0 ≤ ε)
    (hu : K x - ∑ j, ω j * (α j)^2 * normSq (A j x) ≤ u * normSq x)
    (hcost : ∑ j, (K (dressing A (α j) x j) - u * normSq (dressing A (α j) x j)) ≤
      ε * normSq x) :
    let y j := dressing A (α j) x j
    K x + ∑ j, (K (y j) + ω j * normSq (y j) +
      2 * ω j * α j * Phonon.inner (y j) (A j x)) ≤
      (u + ε) * (normSq x + ∑ j, normSq (y j)) := by
  intro y
  have hsplit :
      (∑ j, (K (y j) + ω j * normSq (y j) +
        2 * ω j * α j * Phonon.inner (y j) (A j x))) =
      (∑ j, K (y j)) + ∑ j, (ω j * normSq (y j) +
        2 * ω j * α j * Phonon.inner (y j) (A j x)) := by
    rw [← Finset.sum_add_distrib]
    congr 1
    funext j
    ring
  rw [hsplit, mode_squares]
  have hy (j : m) : (fun i => y j i + α j * A j x i) = 0 := by
    funext i
    simp [y, dressing]
  simp only [hy, normSq_zero, mul_zero, Finset.sum_const_zero, add_zero]
  have hprod : 0 ≤ ε * ∑ j, normSq (y j) :=
    mul_nonneg hε (Finset.sum_nonneg fun j _ => normSq_nonneg (y j))
  change ∑ j, (K (y j) - u * normSq (y j)) ≤ ε * normSq x at hcost
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hcost
  nlinarith only [hu, hprod, hcost]

/-- Interval propagation for a linear signed contrast. -/
theorem contrast_enclosure {ι : Type} [Fintype ι] (w lo hi x : ι → ℝ)
    (hx : ∀ i, lo i ≤ x i ∧ x i ≤ hi i) :
    (∑ i, min (w i * lo i) (w i * hi i)) ≤ ∑ i, w i * x i ∧
    (∑ i, w i * x i) ≤ ∑ i, max (w i * lo i) (w i * hi i) := by
  constructor <;> apply Finset.sum_le_sum <;> intro i _
  · rcases le_total 0 (w i) with h | h
    · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left (hx i).1 h)
    · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left (hx i).2 h)
  · rcases le_total 0 (w i) with h | h
    · exact (mul_le_mul_of_nonneg_left (hx i).2 h).trans (le_max_right _ _)
    · exact (mul_le_mul_of_nonpos_left (hx i).1 h).trans (le_max_left _ _)

/-- Convert trace bounds into free-energy bounds at positive temperature. -/
theorem free_energy_enclosure {t z zlo zhi : ℝ} (ht : 0 < t)
    (hp : 0 < zlo) (hl : zlo ≤ z) (hu : z ≤ zhi) :
    -t * Real.log zhi ≤ -t * Real.log z ∧
      -t * Real.log z ≤ -t * Real.log zlo :=
  ⟨mul_le_mul_of_nonpos_left (Real.log_le_log (hp.trans_le hl) hu) (by linarith),
    mul_le_mul_of_nonpos_left (Real.log_le_log hp hl) (by linarith)⟩

/-- Finite-field pair response per site, after using the number gauge
symmetry to identify the two source signs. -/
theorem four_site_response_enclosure {h f0 fh l0 u0 lh uh : ℝ} (hp : 0 < h)
    (h0 : l0 ≤ f0 ∧ f0 ≤ u0) (hh : lh ≤ fh ∧ fh ≤ uh) :
    (l0 - uh) / (2 * h^2) ≤ (f0 - fh) / (2 * h^2) ∧
      (f0 - fh) / (2 * h^2) ≤ (u0 - lh) / (2 * h^2) :=
  ⟨div_le_div_of_nonneg_right (sub_le_sub h0.1 hh.2) (by positivity),
    div_le_div_of_nonneg_right (sub_le_sub h0.2 hh.1) (by positivity)⟩

end Grain.EFT
