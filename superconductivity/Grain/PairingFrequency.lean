import Grain.PairingCrossing

/-! Positive-frequency sums for the normal-state term and bounds uniform
in the upper frequency cutoff. The Coulomb support is kept fixed. -/

namespace Grain.Pairing.Material

open Finset

def separation (n m : ℕ) : ℕ := (n - m) + (m - n)

noncomputable def profile (modes : List RealMode) (t : ℝ) (k : ℕ) : ℝ :=
  phononResponse modes ((2 * t * k)^2)

theorem transfer_profile (modes : List RealMode) (t : ℝ) (n m : Fin N) :
    phononResponse modes (realTransferSq t n m).1 = profile modes t (separation n m) ∧
    phononResponse modes (realTransferSq t n m).2 = profile modes t (n.val + m.val + 1) := by
  constructor
  · unfold profile realTransferSq frequencyIndex separation
    congr 1
    push_cast
    rcases le_total n.val m.val with h | h
    · rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero, zero_add, Nat.cast_sub h]
      ring
    · rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero, add_zero, Nat.cast_sub h]
      ring
  · unfold profile realTransferSq frequencyIndex
    congr 1
    push_cast
    ring

private theorem sum_difference (f : ℕ → ℝ) (n e : ℕ) :
    (∑ m ∈ range (n + 1 + e), f (separation n m)) =
      (∑ k ∈ range (n + 1), f k) + ∑ k ∈ range e, f (k + 1) := by
  rw [sum_range_add]
  congr 1
  · rw [← sum_range_reflect f (n + 1)]
    apply sum_congr rfl
    intro k hk
    have h : k ≤ n := by simpa using mem_range.mp hk
    simp [separation, Nat.sub_eq_zero_of_le h]
  · apply sum_congr rfl
    intro k _
    congr 1
    unfold separation
    omega

private theorem prefix_shift (f : ℕ → ℝ) (n N : ℕ) :
    (∑ k ∈ range N, f (n + k)) =
      (∑ k ∈ range (n + N), f k) - ∑ k ∈ range n, f k := by
  rw [sum_range_add]
  ring

/-- The difference of the signed normal sums is a short centered sum minus
a translated interval of length 2*n+1 at the cutoff. -/
theorem normal_fold (f : ℕ → ℝ) {n N : ℕ} (hn : n < N) :
    (∑ m ∈ range N, (f (separation n m) - f (n + m + 1))) =
      f 0 + 2 * (∑ k ∈ range n, f (k + 1)) -
      ∑ k ∈ range (2 * n + 1), f (N - n + k) := by
  rw [sum_sub_distrib]
  have hd : (∑ m ∈ range N, f (separation n m)) =
      (∑ k ∈ range (n + 1), f k) + ∑ k ∈ range (N - (n + 1)), f (k + 1) := by
    conv_lhs => rw [show N = n + 1 + (N - (n + 1)) by omega]
    exact sum_difference f n _
  simp only [show ∀ k : ℕ, n + k + 1 = n + 1 + k by omega]
  have hs' : (∑ k ∈ range (N - (n + 1)), f (k + 1)) =
      ∑ k ∈ range (N - (n + 1)), f (1 + k) := by simp only [Nat.add_comm 1]
  rw [hs'] at hd
  rw [hd, prefix_shift f (n + 1), prefix_shift f 1, prefix_shift f (N - n)]
  rw [show 1 + (N - (n + 1)) = N - n by omega,
    show N - n + (2 * n + 1) = n + 1 + N by omega]
  have hs := sum_range_succ' f n
  rw [sum_range_one] 
  rw [hs]
  ring

/-- Numerator of the all-frequency normal metric. The folded series
telescopes to transfers from zero through n. -/
noncomputable def fullMetric [Fintype p] (b : Mesh p) (r : Realization p)
    (t : ℝ) (a : p × ℕ) : ℝ :=
  ((2 * (a.2 : ℝ) + 1) + ∑ j, dos b r j *
    (profile (r.modes a.1 j) t 0 + 2 * (∑ k ∈ range a.2, profile (r.modes a.1 j) t (k + 1)))) /
    dos b r a.1

theorem fullMetric_sub_meshMetric [Fintype p] (b : Mesh p) (r : Realization p)
    (t : ℝ) (a : p × Fin N) :
    fullMetric b r t (a.1, a.2.val) - meshMetric b r t a =
      (∑ j, dos b r j * (∑ k ∈ range (2 * a.2.val + 1),
        profile (r.modes a.1 j) t (N - a.2.val + k))) / dos b r a.1 := by
  unfold fullMetric meshMetric
  simp only [Fintype.sum_prod_type, transfer_profile, ← mul_sum,
    frequencyIndex, Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast, Rat.cast_one]
  have hn (j : p) := Fin.sum_univ_eq_sum_range
    (fun k => profile (r.modes a.1 j) t (separation a.2.val k) -
      profile (r.modes a.1 j) t (a.2.val + k + 1)) N
  simp_rw [hn, normal_fold _ a.2.isLt, mul_sub, sum_sub_distrib]
  rw [← sub_div]
  congr 1
  ring

/-- Sum of the oscillator-response numerators 2 Ω |g|². -/
noncomputable def profileMoment (modes : List RealMode) : ℝ :=
  (modes.map fun m => 2 * m.energy * m.vertexSq).sum

theorem profile_bounds (boxes : List ModeBox) (modes : List RealMode)
    (h : List.Forall₂ ModeBox.matches boxes modes) (t : ℝ) (k : ℕ) :
    0 ≤ profile modes t k ∧ 0 ≤ profileMoment modes ∧
      (k ≠ 0 → t ≠ 0 → profile modes t k ≤ (profileMoment modes / (4*t^2)) / (k : ℝ)^2) := by
  induction h with
  | nil => simp [profile, phononResponse, profileMoment]
  | @cons box mode _ _ hm _ ih =>
    have he : 0 < mode.energy := (by exact_mod_cast hm.1 : (0 : ℝ) < box.energy.lo).trans_le hm.2.2.1.1
    have hg : 0 ≤ mode.vertexSq := (by exact_mod_cast hm.2.1 : (0 : ℝ) ≤ box.vertexSq.lo).trans hm.2.2.2.1
    simp only [profile, phononResponse, profileMoment, List.map_cons, List.sum_cons, modeResponse] at *
    refine ⟨add_nonneg (by positivity) ih.1, add_nonneg (by positivity) ih.2.1, fun hk ht => ?_⟩
    rw [add_div, add_div]
    apply add_le_add _ (ih.2.2 hk ht)
    rw [div_div]
    apply div_le_div_of_nonneg_left (by positivity) _ _
    · positivity
    · nlinarith only [sq_nonneg mode.energy]

private theorem translated_sum_bound {f : ℕ → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hf : ∀ k : ℕ, k ≠ 0 → f k ≤ A / (k : ℝ)^2) {L : ℕ} (hL : 0 < L) (e : ℕ) :
    (∑ k ∈ range e, f (L + k)) ≤ 2 * A * (1 / (L : ℝ) - 1 / ((L : ℝ) + e)) := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [sum_range_succ]
    have h := hf (L + e) (by omega)
    push_cast at h
    let a : ℝ := (L : ℝ) + e
    have ha : 1 ≤ a := by
      dsimp [a]
      have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
      linarith [Nat.cast_nonneg (α := ℝ) e]
    have hb : A / a^2 ≤ 2 * A * (1 / a - 1 / (a + 1)) := by
      have hp : 0 < a := by linarith
      have hp' : 0 < a + 1 := by positivity
      rw [show 1 / a - 1 / (a + 1) = 1 / (a * (a + 1)) by field_simp; ring]
      rw [mul_one_div]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      nlinarith only [mul_nonneg (mul_nonneg hA hp.le) (sub_nonneg.mpr ha)]
    push_cast
    rw [← add_assoc]
    change _ ≤ 2 * A * (1 / (L : ℝ) - 1 / (a + 1))
    linarith only [ih, h, hb]

/-- Explicit bound on the error in each retained metric entry. The
estimate decays as (N-n)⁻² for fixed n. -/
theorem fullMetric_error [Fintype p] (b : Mesh p) (r : Realization p) (h : b.matches r)
    (w : ∀ i, 0 < dos b r i) (t : ℝ) (ht : t ≠ 0) (a : p × Fin N) :
    0 ≤ fullMetric b r t (a.1, a.2.val) - meshMetric b r t a ∧
    fullMetric b r t (a.1, a.2.val) - meshMetric b r t a ≤
      (∑ j, dos b r j * ((2 * (a.2.val : ℝ) + 1) *
        ((profileMoment (r.modes a.1 j) / (4*t^2)) / ((N - a.2.val : ℕ) : ℝ)^2))) /
        dos b r a.1 := by
  rw [fullMetric_sub_meshMetric]
  constructor
  · exact div_nonneg (sum_nonneg fun j _ => mul_nonneg (w j).le
      (sum_nonneg fun _ _ => (profile_bounds _ _ (h.2.1 _ _) t _).1)) (w a.1).le
  · apply div_le_div_of_nonneg_right _ (w a.1).le
    apply sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_left _ (w j).le
    let C := (profileMoment (r.modes a.1 j) / (4*t^2)) / ((N - a.2.val : ℕ) : ℝ)^2
    have he : (∑ _k ∈ range (2 * a.2.val + 1), C) = (2 * (a.2.val : ℝ) + 1) * C := by
      rw [sum_const, card_range, nsmul_eq_mul]
      push_cast
      ring
    change _ ≤ (2 * (a.2.val : ℝ) + 1) * C
    rw [← he]
    apply sum_le_sum
    intro k _
    have hL : 0 < N - a.2.val := Nat.sub_pos_of_lt a.2.isLt
    have hv := profile_bounds _ _ (h.2.1 a.1 j) t (N - a.2.val + k)
    apply (hv.2.2 (by omega) ht).trans
    apply div_le_div_of_nonneg_left (div_nonneg hv.2.1 (by positivity)) (by exact_mod_cast pow_pos hL 2)
    exact_mod_cast (Nat.pow_le_pow_left (by omega : N - a.2.val ≤ N - a.2.val + k) 2)

private theorem shifted_profile_bound {f : ℕ → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hf : ∀ k : ℕ, k ≠ 0 → f k ≤ A / (k : ℝ)^2) {L : ℕ} (hL : 0 < L) (e : ℕ) :
    (∑ k ∈ range e, f (L + k)) ≤ 2 * A / (L : ℝ) := by
  refine (translated_sum_bound hA hf hL e).trans ?_
  calc
    _ ≤ 2 * A * (1 / (L : ℝ)) := mul_le_mul_of_nonneg_left
      (sub_le_self (1 / (L : ℝ)) (by positivity : 0 ≤ 1 / ((L : ℝ) + e))) (by positivity)
    _ = _ := by ring

/-- For a fixed row, the sum of the two folded transfer terms is at
most the sum over all signed bosonic transfers. -/
theorem folded_row_bound {f : ℕ → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hp : ∀ k, 0 ≤ f k) (hf : ∀ k : ℕ, k ≠ 0 → f k ≤ A / (k : ℝ)^2)
    (n N : ℕ) :
    (∑ m ∈ range N, (f (separation n m) + f (n + m + 1))) ≤ f 0 + 4 * A := by
  let M := max N (n + 1)
  have hn : n < M := lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
  have hNM : N ≤ M := le_max_left _ _
  refine (sum_le_sum_of_subset_of_nonneg (range_mono hNM)
    (fun _ _ _ => add_nonneg (hp _) (hp _))).trans ?_
  rw [sum_add_distrib]
  have hd : (∑ m ∈ range M, f (separation n m)) =
      (∑ k ∈ range (n + 1), f k) + ∑ k ∈ range (M - (n + 1)), f (1 + k) := by
    conv_lhs => rw [show M = n + 1 + (M - (n + 1)) by omega]
    simpa only [Nat.add_comm 1] using sum_difference f n (M - (n + 1))
  simp only [show ∀ k : ℕ, n + k + 1 = 1 + (n + k) by omega]
  rw [hd, sum_range_succ']
  have hl := shifted_profile_bound hA hf (L := 1) (by decide) (n + M)
  have hs : (∑ k ∈ range n, f (1 + k)) + (∑ k ∈ range M, f (1 + (n + k))) ≤ 2 * A := by
    rw [← sum_range_add (fun k => f (1 + k))]
    simpa using hl
  have he := shifted_profile_bound hA hf (L := 1) (by decide) (M - (n + 1))
  norm_num at he
  simp only [Nat.add_comm 1] at hs he ⊢
  linarith

/-- Bound on the interaction with every additional frequency, for a
retained row. Coulomb is absent from these columns when its cutoff is
at most N. -/
theorem folded_tail_bound {f : ℕ → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hf : ∀ k : ℕ, k ≠ 0 → f k ≤ A / (k : ℝ)^2) {n N : ℕ} (hn : n < N) (e : ℕ) :
    (∑ m ∈ range e, (f (separation n (N + m)) + f (n + (N + m) + 1))) ≤
    2 * A / ((N - n : ℕ) : ℝ) + 2 * A / ((n + N + 1 : ℕ) : ℝ) := by
  simp only [sum_add_distrib, show ∀ k : ℕ, separation n (N + k) = (N - n) + k by
    intro k
    unfold separation
    omega, show ∀ k : ℕ, n + (N + k) + 1 = n + N + 1 + k by omega]
  exact add_le_add (shifted_profile_bound hA hf (by omega) e)
    (shifted_profile_bound hA hf (by omega) e)

theorem fullMetric_ge_bare [Fintype p] (b : Mesh p) (r : Realization p)
    (h : b.matches r) (w : ∀ i, 0 < dos b r i) (t : ℝ) (a : p × ℕ) :
    (2 * (a.2 : ℝ) + 1) / dos b r a.1 ≤ fullMetric b r t a := by
  unfold fullMetric
  apply div_le_div_of_nonneg_right _ (w a.1).le
  apply le_add_of_nonneg_right
  exact sum_nonneg fun j _ => mul_nonneg (w j).le
    (add_nonneg (profile_bounds _ _ (h.2.1 _ _) t _).1
      (mul_nonneg (by norm_num) (sum_nonneg fun _ _ => (profile_bounds _ _ (h.2.1 _ _) t _).1)))

/-- Symmetric entrywise uncertainty gives a quadratic bound from row
sums. This version applies to real residuals, including other errors
in a projected pairing kernel. -/
theorem realForm_abs_le_row {ι : Type} [Fintype ι] (A : ι → ι → ℝ)
    (hs : ∀ i j, A i j = A j i) (x : ι → ℝ) :
    |realForm A x| ≤ ∑ i, (∑ j, |A i j|) * (x i)^2 := by
  let f (i j : ι) := |A i j| * (x i)^2 / 2
  have hterm (i j : ι) : |A i j * (x i * x j)| ≤ f i j + f j i := by
    rw [abs_mul, abs_mul]
    have h : |x i| * |x j| ≤ ((x i)^2 + (x j)^2) / 2 := by
      nlinarith only [sq_nonneg (|x i| - |x j|), sq_abs (x i), sq_abs (x j)]
    calc
      _ ≤ |A i j| * (((x i)^2 + (x j)^2) / 2) := mul_le_mul_of_nonneg_left h (abs_nonneg _)
      _ = _ := by dsimp [f]; rw [hs j i]; ring
  calc
    _ ≤ ∑ i, ∑ j, |A i j * (x i * x j)| :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun _ _ => abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ j, (f i j + f j i) := sum_le_sum fun _ _ => sum_le_sum fun _ _ => hterm _ _
    _ = _ := by
      simp only [sum_add_distrib]
      rw [sum_comm (f := fun i j => f j i), ← sum_add_distrib]
      refine sum_congr rfl fun i _ => ?_
      rw [← sum_add_distrib, sum_mul]
      exact sum_congr rfl fun j _ => by dsimp [f]; ring

end Grain.Pairing.Material
