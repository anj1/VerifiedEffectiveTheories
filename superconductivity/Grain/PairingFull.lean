import Grain.PairingFrequency
import Mathlib.Topology.UniformSpace.UniformApproximation

/-! Form bounds for adding arbitrarily many Matsubara frequencies. -/

namespace Grain.Pairing.Material

open Finset

variable {p : Type} [Fintype p]

noncomputable def frequencyMetric (b : Mesh p) (r : Realization p) (t : ℝ) (a : p × Fin N) : ℝ :=
  fullMetric b r t (a.1, a.2.val)

theorem frequencyMetric_pos (b : Mesh p) (r : Realization p) (h : b.matches r)
    (w : ∀ i, 0 < dos b r i) (t : ℝ) (a : p × Fin N) :
    0 < frequencyMetric b r t a := by
  have hb : 0 < (2 * (a.2.val : ℝ) + 1) / dos b r a.1 := div_pos (by positivity) (w a.1)
  exact hb.trans_le (fullMetric_ge_bare b r h w t (a.1, a.2.val))

private theorem grid_split {M : Type} [AddCommMonoid M] {N e : ℕ} (f : p × Fin (N + e) → M) :
    (∑ i, f i) = (∑ i : p × Fin N, f (i.1, Fin.castAdd e i.2)) +
      ∑ i : p × Fin e, f (i.1, Fin.natAdd N i.2) := by
  simp_rw [Fintype.sum_prod_type, Fin.sum_univ_add, sum_add_distrib]

private def retainedKernel (F : (p × Fin (N + e)) → (p × Fin (N + e)) → ℝ)
    (i j : p × Fin (N + e)) : ℝ :=
  if i.2.val < N ∧ j.2.val < N then F i j else 0

private theorem retained_form (F : (p × Fin (N + e)) → (p × Fin (N + e)) → ℝ)
    (x : p × Fin (N + e) → ℝ) :
    realForm (retainedKernel F) x =
      realForm (fun i j : p × Fin N => F (i.1, Fin.castAdd e i.2) (j.1, Fin.castAdd e j.2))
        (fun i => x (i.1, Fin.castAdd e i.2)) := by
  unfold realForm
  rw [grid_split]
  simp only [retainedKernel, Fin.val_natAdd, show ∀ k : Fin e, ¬ N + k.val < N by omega,
    false_and, ite_false, zero_mul, sum_const_zero, add_zero]
  apply sum_congr rfl
  intro i _
  rw [grid_split]
  simp [i.2.isLt, show ∀ k : Fin e, ¬ N + k.val < N by omega]

/-- Bounds for a retained row and for any row past the retained grid,
using upper bounds on P(0) and its inverse-square decay coefficient. -/
noncomputable def retainedAllowance (A : p → p → ℝ) (a : p × Fin N) : ℝ :=
  ∑ j, (2 * A a.1 j / ((N - a.2.val : ℕ) : ℝ) +
    2 * A a.1 j / ((a.2.val + N + 1 : ℕ) : ℝ))

noncomputable def discardedAllowance (P A : p → p → ℝ) (i : p) : ℝ :=
  ∑ j, (P i j + 4 * A i j)

/-- The residual when the pairing interaction is set to zero outside
the retained block is bounded independently of the larger grid. -/
private theorem tail_rows (r : Realization p) (t : ℝ) (cutoff N e : ℕ)
    (hcut : cutoff ≤ N) (P A : p → p → ℝ)
    (hP : ∀ i j, profile (r.modes i j) t 0 ≤ P i j)
    (hA : ∀ i j, 0 ≤ A i j)
    (hp : ∀ i j k, 0 ≤ profile (r.modes i j) t k)
    (ha : ∀ i j (k : ℕ), k ≠ 0 → profile (r.modes i j) t k ≤ A i j / (k : ℝ)^2) :
    let F := meshKernel r cutoff t (N := N + e)
    let R := fun i j => F i j - retainedKernel F i j
    (∀ a : p × Fin N,
      (∑ j, |R (a.1, Fin.castAdd e a.2) j|) ≤ retainedAllowance A a) ∧
    (∀ a : p × Fin e,
      (∑ j, |R (a.1, Fin.natAdd N a.2) j|) ≤ discardedAllowance P A a.1) := by
  dsimp only
  have hre (a d : p × Fin (N + e)) (h : ¬ (a.2.val < N ∧ d.2.val < N)) :
      |meshKernel r cutoff t a d - retainedKernel (meshKernel r cutoff t) a d| =
        profile (r.modes a.1 d.1) t (separation a.2.val d.2.val) +
          profile (r.modes a.1 d.1) t (a.2.val + d.2.val + 1) := by
    have hc : ¬ (a.2.val < cutoff ∧ d.2.val < cutoff) :=
      fun ⟨h₁, h₂⟩ => h ⟨h₁.trans_le hcut, h₂.trans_le hcut⟩
    simp only [retainedKernel, meshKernel, h, hc, ite_false, sub_zero, transfer_profile]
    exact abs_of_nonneg (add_nonneg (hp _ _ _) (hp _ _ _))
  constructor
  · intro a
    rw [grid_split]
    have hz : (∑ j : p × Fin N, |meshKernel r cutoff t (a.1, Fin.castAdd e a.2)
        (j.1, Fin.castAdd e j.2) - retainedKernel (meshKernel r cutoff t)
        (a.1, Fin.castAdd e a.2) (j.1, Fin.castAdd e j.2)|) = 0 := by
      simp [retainedKernel, a.2.isLt]
    rw [hz, zero_add, Fintype.sum_prod_type]
    apply sum_le_sum
    intro j _
    have he (k : Fin e) := hre (a.1, Fin.castAdd e a.2) (j, Fin.natAdd N k)
      (fun h => by have := h.2; simp only [Fin.val_natAdd] at this; omega)
    simp_rw [he, Fin.val_castAdd, Fin.val_natAdd]
    exact (Fin.sum_univ_eq_sum_range
      (fun k => profile (r.modes a.1 j) t (separation a.2.val (N + k)) +
        profile (r.modes a.1 j) t (a.2.val + (N + k) + 1)) e).le.trans
      (folded_tail_bound (hA a.1 j) (ha a.1 j) a.2.isLt e)
  · intro a
    rw [Fintype.sum_prod_type]
    apply sum_le_sum
    intro j _
    have he (k : Fin (N + e)) := hre (a.1, Fin.natAdd N a.2) (j, k)
      (fun h => by have := h.1; simp only [Fin.val_natAdd] at this; omega)
    simp_rw [he, Fin.val_natAdd]
    rw [Fin.sum_univ_eq_sum_range
      (fun k => profile (r.modes a.1 j) t (separation (N + a.2.val) k) +
        profile (r.modes a.1 j) t (N + a.2.val + k + 1)) (N + e)]
    exact (folded_row_bound (hA a.1 j) (hp a.1 j) (ha a.1 j) _ _).trans
      (add_le_add_left (hP a.1 j) _)

/-- A retained pencil with a diagonal allowance certifies an upper
bound on every larger grid with the all-frequency normal metric. -/
theorem all_grids_upper (b : Mesh p) (r : Realization p) (h : b.matches r)
    (w : ∀ i, 0 < dos b r i) (t : ℝ) (ht : t ≠ 0) (cutoff N : ℕ)
    (hcut : cutoff ≤ N) (hm : ∀ i j, r.modes i j = r.modes j i)
    (hc : ∀ i j, r.coulomb i j = r.coulomb j i)
    (P A : p → p → ℝ) (hP : ∀ i j, profile (r.modes i j) t 0 ≤ P i j)
    (hA : ∀ i j, profileMoment (r.modes i j) / (4*t^2) ≤ A i j)
    (u : ℝ) (hu : 0 ≤ u)
    (hhead : ∀ x : p × Fin N → ℝ, realForm (meshKernel r cutoff t) x +
      realMetric (retainedAllowance A) x ≤ u * realMetric (frequencyMetric b r t) x)
    (htail : ∀ i, discardedAllowance P A i ≤ u * ((2 * (N : ℝ) + 1) / dos b r i))
    (e : ℕ) (x : p × Fin (N + e) → ℝ) :
    realForm (meshKernel r cutoff t) x ≤ u * realMetric (frequencyMetric b r t) x := by
  let F := meshKernel r cutoff t (N := N + e)
  let R := fun i j => F i j - retainedKernel F i j
  have hp (i j : p) (k : ℕ) := profile_bounds _ _ (h.2.1 i j) t k
  have hA0 (i j : p) := (div_nonneg (hp i j 0).2.1 (by positivity)).trans (hA i j)
  obtain ⟨hleft, hright⟩ := tail_rows r t cutoff N e hcut P A hP hA0
    (fun i j k => (hp i j k).1) (fun i j k hk => ((hp i j k).2.2 hk ht).trans
      (div_le_div_of_nonneg_right (hA i j) (sq_nonneg _)))
  have hsym (i j : p × Fin (N + e)) : R i j = R j i := by
    have hf : F i j = F j i := mesh_kernel_symm r cutoff t hm hc i j
    by_cases hn : i.2.val < N ∧ j.2.val < N
    · simp [R, retainedKernel, hn]
    · have hn' : ¬ (j.2.val < N ∧ i.2.val < N) := fun h => hn ⟨h.2, h.1⟩
      simp [R, retainedKernel, hn, hn', hf]
  have hsplit : realForm F x = realForm (retainedKernel F) x + realForm R x := by
    simp only [realForm, R, sub_mul, sum_sub_distrib]
    ring
  let y (i : p × Fin N) := x (i.1, Fin.castAdd e i.2)
  let z (i : p × Fin e) := x (i.1, Fin.natAdd N i.2)
  have hb := (le_abs_self (realForm R x)).trans (realForm_abs_le_row R hsym x)
  rw [grid_split] at hb
  have hrest (a : p × Fin e) :
      (∑ j, |R (a.1, Fin.natAdd N a.2) j|) ≤ u * frequencyMetric b r t (a.1, Fin.natAdd N a.2) := by
    apply (hright a).trans ((htail a.1).trans _)
    apply mul_le_mul_of_nonneg_left _ hu
    apply le_trans _ (fullMetric_ge_bare b r h w t (a.1, N + a.2.val))
    apply div_le_div_of_nonneg_right _ (w a.1).le
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) a.2.val]
  have hbound : realForm R x ≤ realMetric (retainedAllowance A) y +
      u * ∑ i : p × Fin e, frequencyMetric b r t (i.1, Fin.natAdd N i.2) * (z i)^2 := by
    apply hb.trans
    rw [mul_sum]
    exact add_le_add (sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hleft i) (sq_nonneg _))
      (sum_le_sum fun i _ => by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (hrest i) (sq_nonneg _))
  rw [hsplit, retained_form]
  change realForm (meshKernel r cutoff t) y + realForm R x ≤ _
  unfold realMetric at *
  rw [grid_split, mul_add]
  have hh := hhead y
  change realForm (meshKernel r cutoff t) y + _ ≤
    u * (∑ i : p × Fin N, frequencyMetric b r t i * (y i)^2) +
      u * ∑ i : p × Fin e, frequencyMetric b r t (i.1, Fin.natAdd N i.2) * (z i)^2
  linarith only [hh, hbound]

private theorem grid_form_extension (b : Mesh p) (r : Realization p) (t : ℝ)
    (cutoff N M : ℕ) (hnm : N ≤ M) (x : p × Fin N → ℝ) :
    ∃ y : p × Fin M → ℝ,
      realForm (meshKernel r cutoff t) y = realForm (meshKernel r cutoff t) x ∧
      realMetric (frequencyMetric b r t) y = realMetric (frequencyMetric b r t) x := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hnm
  let y (a : p × Fin (N + e)) := if h : a.2.val < N then x (a.1, ⟨a.2.val, h⟩) else 0
  have h₁ (a : p × Fin N) : y (a.1, Fin.castAdd e a.2) = x a := by
    rcases a with ⟨i, n⟩
    simp [y, n.isLt]
  have h₂ (a : p × Fin e) : y (a.1, Fin.natAdd N a.2) = 0 := by
    simp [y, show ¬ N + a.2.val < N by omega]
  refine ⟨y, ?_, ?_⟩
  · unfold realForm
    rw [grid_split]
    simp only [h₂, zero_mul, mul_zero, sum_const_zero, add_zero, h₁]
    refine sum_congr rfl fun i _ => ?_
    rw [grid_split]
    simp only [h₁, h₂, mul_zero, sum_const_zero, add_zero]
    rfl
  · unfold realMetric
    rw [grid_split]
    simp only [h₁, h₂, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      mul_zero, sum_const_zero, add_zero]
    rfl

/-- The variational spectrum on finitely supported frequency vectors.
Including zero gives the top of the spectrum with the accumulation
point at zero included. -/
noncomputable def allFrequencyTop (b : Mesh p) (r : Realization p) (cutoff : ℕ) (t : ℝ) : ℝ :=
  sSup (insert 0 (⋃ N : ℕ, values (meshKernel r cutoff t (N := N)) (frequencyMetric b r t)))

private theorem all_frequency_upper_gap (b : Mesh p) (r : Realization p)
    (cutoff : ℕ) (t : ℝ) (N : ℕ) {u : ℝ} (hu : 0 ≤ u)
    (hlarge : ∀ e (x : p × Fin (N + e) → ℝ),
      realForm (meshKernel r cutoff t) x ≤ u * realMetric (frequencyMetric b r t) x) :
    ∀ q ∈ insert (0 : ℝ) (⋃ M : ℕ, values (meshKernel r cutoff t (N := M))
      (frequencyMetric b r t)), q ≤ u := by
  intro q hq
  rcases Set.mem_insert_iff.mp hq with rfl | hq
  · exact hu
  obtain ⟨M, x, hx, rfl⟩ := Set.mem_iUnion.mp hq
  obtain ⟨y, hyF, hyD⟩ := grid_form_extension b r t cutoff M (N + M) (by omega) x
  exact (div_le_iff₀ hx).2 (by simpa only [hyF, hyD] using hlarge M y)

theorem all_frequency_upper (b : Mesh p) (r : Realization p)
    (cutoff : ℕ) (t : ℝ) (N : ℕ) {u : ℝ} (hu : 0 ≤ u)
    (hlarge : ∀ e (x : p × Fin (N + e) → ℝ),
      realForm (meshKernel r cutoff t) x ≤ u * realMetric (frequencyMetric b r t) x) :
    allFrequencyTop b r cutoff t ≤ u :=
  csSup_le ⟨0, Set.mem_insert _ _⟩ (all_frequency_upper_gap b r cutoff t N hu hlarge)

noncomputable def totalAllowance (b : Mesh p) (r : Realization p) (P A : p → p → ℝ) : ℝ :=
  ∑ i, dos b r i * discardedAllowance P A i

private theorem allowance_div_N (A : p → p → ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (a : p × Fin N) :
    retainedAllowance A a ≤ (2 * (a.2.val : ℝ) + 1) / (N : ℝ) * ∑ j, 4 * A a.1 j := by
  have hn : (0 : ℝ) < N := by exact_mod_cast Nat.zero_lt_of_lt a.2.isLt
  let n : ℝ := a.2.val
  let N' : ℝ := N
  have hn0 : 0 ≤ n := by dsimp [n]; positivity
  have hgap : 1 ≤ N' - n := by
    dsimp [n, N']
    have h : (a.2.val : ℝ) + 1 ≤ N := by exact_mod_cast a.2.isLt
    linarith
  have hb : N' ≤ (N' - n) * (2*n + 1) := by
    nlinarith only [mul_nonneg hn0 (sub_nonneg.mpr hgap), hn0]
  have hc : N' ≤ (n + N' + 1) * (2*n + 1) := by
    nlinarith only [mul_nonneg hn0 (by dsimp [N']; positivity : 0 ≤ N'),
      sq_nonneg n, hn0]
  rw [retainedAllowance, mul_sum]
  apply sum_le_sum
  intro j _
  have ha := hA a.1 j
  rw [Nat.cast_sub a.2.isLt.le]
  push_cast
  change 2 * A a.1 j / (N' - n) + 2 * A a.1 j / (n + N' + 1) ≤
    (2*n + 1) / N' * (4 * A a.1 j)
  have hleft : 1 / (N' - n) ≤ (2*n+1) / N' :=
    (div_le_div_iff₀ (by linarith) hn).2 (by linarith only [hb])
  have hright : 1 / (n + N' + 1) ≤ (2*n+1) / N' :=
    (div_le_div_iff₀ (by dsimp [N']; positivity) hn).2 (by linarith only [hc])
  have hsum := mul_le_mul_of_nonneg_left (add_le_add hleft hright) (by positivity : 0 ≤ 2 * A a.1 j)
  linarith only [hsum, show 2 * A a.1 j * (1 / (N' - n) + 1 / (n + N' + 1)) =
    2 * A a.1 j / (N' - n) + 2 * A a.1 j / (n + N' + 1) by ring,
    show 2 * A a.1 j * ((2*n+1) / N' + (2*n+1) / N') =
      (2*n+1) / N' * (4 * A a.1 j) by ring]

set_option maxHeartbeats 1000000 in
theorem all_frequency_enclosure (b : Mesh p) (r : Realization p) (h : b.matches r)
    (w : ∀ i, 0 < dos b r i) (t : ℝ) (ht : t ≠ 0) (cutoff N : ℕ)
    (hcut : cutoff ≤ N) (hN : 0 < N)
    (hm : ∀ i j, r.modes i j = r.modes j i) (hc : ∀ i j, r.coulomb i j = r.coulomb j i)
    (P A : p → p → ℝ) (hP : ∀ i j, profile (r.modes i j) t 0 ≤ P i j)
    (hA : ∀ i j, profileMoment (r.modes i j) / (4*t^2) ≤ A i j) :
    let q := max 0 (spectrumTop (meshKernel r cutoff t (N := N)) (frequencyMetric b r t))
    q ≤ allFrequencyTop b r cutoff t ∧
    allFrequencyTop b r cutoff t ≤ q + totalAllowance b r P A / (N : ℝ) := by
  dsimp only
  let q := max 0 (spectrumTop (meshKernel r cutoff t (N := N)) (frequencyMetric b r t))
  let C := totalAllowance b r P A
  let δ := C / (N : ℝ)
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have ha (i j : p) := (div_nonneg (profile_bounds _ _ (h.2.1 i j) t 0).2.1
    (by positivity)).trans (hA i j)
  have hp (i j : p) := (profile_bounds _ _ (h.2.1 i j) t 0).1.trans (hP i j)
  have hb (i : p) : 0 ≤ discardedAllowance P A i :=
    sum_nonneg fun j _ => add_nonneg (hp i j) (mul_nonneg (by norm_num) (ha i j))
  have hC : 0 ≤ C := sum_nonneg fun i _ => mul_nonneg (w i).le (hb i)
  have hδ : 0 ≤ δ := div_nonneg hC hn.le
  have hi (i : p) : discardedAllowance P A i ≤ C / dos b r i := by
    apply (le_div_iff₀ (w i)).2
    rw [mul_comm]
    exact single_le_sum (fun j _ => mul_nonneg (w j).le (hb j)) (mem_univ i)
  have hh (a : p × Fin N) : retainedAllowance A a ≤ δ * frequencyMetric b r t a := by
    calc
      _ ≤ (2 * (a.2.val : ℝ) + 1) / (N : ℝ) * ∑ j, 4 * A a.1 j := allowance_div_N A ha a
      _ ≤ (2 * (a.2.val : ℝ) + 1) / (N : ℝ) * (C / dos b r a.1) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (sum_le_sum fun j _ => le_add_of_nonneg_left (hp a.1 j)).trans (hi a.1)
      _ = δ * ((2 * (a.2.val : ℝ) + 1) / dos b r a.1) := by dsimp [δ]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (fullMetric_ge_bare b r h w t (a.1, a.2.val)) hδ
  have hq : 0 ≤ q := le_max_left _ _
  have hhead (x : p × Fin N → ℝ) :
      realForm (meshKernel r cutoff t) x + realMetric (retainedAllowance A) x ≤
        (q + δ) * realMetric (frequencyMetric b r t) x := by
    rw [add_mul]
    have hx : 0 ≤ realMetric (frequencyMetric b r t) x :=
      sum_nonneg fun a _ => mul_nonneg (frequencyMetric_pos b r h w t a).le (sq_nonneg _)
    refine add_le_add ((form_le_spectrum _ _ (frequencyMetric_pos b r h w t) x).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hx)) ?_
    simp only [realMetric, mul_sum, ← mul_assoc]
    exact sum_le_sum fun a _ => mul_le_mul_of_nonneg_right (hh a) (sq_nonneg _)
  have htai (i : p) : discardedAllowance P A i ≤ (q + δ) * ((2 * (N : ℝ) + 1) / dos b r i) := by
    refine (hi i).trans ?_
    calc
      C / dos b r i = δ * ((N : ℝ) / dos b r i) := by dsimp [δ]; field_simp
      _ ≤ (q + δ) * ((2 * (N : ℝ) + 1) / dos b r i) := by
        exact mul_le_mul (le_add_of_nonneg_left hq) (div_le_div_of_nonneg_right (by linarith) (w i).le)
          (div_nonneg hn.le (w i).le) (add_nonneg hq hδ)
  have huv := all_frequency_upper_gap b r cutoff t N (add_nonneg hq hδ)
    (fun e => all_grids_upper b r h w t ht cutoff N hcut hm hc P A hP hA
      (q + δ) (add_nonneg hq hδ) hhead htai e)
  have hupper := csSup_le ⟨0, Set.mem_insert _ _⟩ huv
  refine ⟨max_le (le_csSup ⟨_, huv⟩ (Set.mem_insert _ _)) ?_, hupper⟩
  by_cases he : (values (meshKernel r cutoff t (N := N)) (frequencyMetric b r t)).Nonempty
  · exact csSup_le he fun x hx => le_csSup ⟨_, huv⟩ (Set.mem_insert_of_mem _
      (Set.mem_iUnion.mpr ⟨N, hx⟩))
  · rw [spectrumTop, Set.not_nonempty_iff_eq_empty.mp he, Real.sSup_empty]
    exact le_csSup ⟨_, huv⟩ (Set.mem_insert _ _)

open Set Filter

private theorem frequency_spectrum_continuous (b : Mesh p) (r : Realization p)
    (h : b.matches r) (w : ∀ i, 0 < dos b r i) (cutoff N : ℕ) :
    Continuous fun t : ℝ => spectrumTop (meshKernel r cutoff t (N := N)) (frequencyMetric b r t) := by
  apply spectrum_continuous _ _ _ _ (frequencyMetric_pos b r h w)
  · intro a d
    have hv := continuous_transfers a.2 d.2
    have h₁ := continuous_phonon _ _ (h.2.1 a.1 d.1) _ hv.1 (fun _ => sq_nonneg _)
    have h₂ := continuous_phonon _ _ (h.2.1 a.1 d.1) _ hv.2 (fun _ => sq_nonneg _)
    unfold meshKernel
    dsimp only
    split
    · exact (h₁.add h₂).sub continuous_const
    · exact h₁.add h₂
  · intro a
    have hp (i j : p) (k : ℕ) : Continuous fun t : ℝ => profile (r.modes i j) t k :=
      continuous_phonon _ _ (h.2.1 i j) _
        ((continuous_const.mul continuous_id |>.mul continuous_const).pow 2) (fun _ => sq_nonneg _)
    unfold frequencyMetric fullMetric
    apply Continuous.div_const
    exact continuous_const.add (continuous_finsetSum _ fun j _ =>
      continuous_const.mul ((hp a.1 j 0).add
        (continuous_const.mul (continuous_finsetSum _ fun k _ => hp a.1 j (k + 1)))))

theorem all_frequency_continuous (b : Mesh p) (r : Realization p) (h : b.matches r)
    (w : ∀ i, 0 < dos b r i) (cutoff : ℕ)
    (hm : ∀ i j, r.modes i j = r.modes j i) (hc : ∀ i j, r.coulomb i j = r.coulomb j i)
    {cold : ℝ} (h0 : 0 < cold) :
    ContinuousOn (allFrequencyTop b r cutoff) (Ici cold) := by
  let G (N : ℕ) (t : ℝ) := max 0 (spectrumTop (meshKernel r cutoff t (N := N))
    (frequencyMetric b r t))
  let P (i j : p) := profile (r.modes i j) cold 0
  let A (i j : p) := profileMoment (r.modes i j) / (4*cold^2)
  have hconv : TendstoUniformlyOn G (allFrequencyTop b r cutoff) atTop (Ici cold) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hlim : Tendsto (fun n : ℕ => totalAllowance b r P A / (n : ℝ)) atTop (nhds 0) := by
      simpa only [Function.comp_apply, div_eq_mul_inv, mul_zero] using (tendsto_inv_atTop_zero.comp
        (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul (totalAllowance b r P A)
    filter_upwards [hlim.eventually (gt_mem_nhds hε), eventually_ge_atTop cutoff,
      eventually_ge_atTop 1] with N he hcut hN t ht
    have ht' : cold ≤ t := ht
    have hP (i j : p) : profile (r.modes i j) t 0 ≤ P i j := by simp [P, profile]
    have a (i j : p) : profileMoment (r.modes i j) / (4*t^2) ≤ A i j := by
      apply div_le_div_of_nonneg_left (profile_bounds _ _ (h.2.1 i j) cold 0).2.1 (by positivity)
      nlinarith only [mul_nonneg (sub_nonneg.mpr ht') (show 0 ≤ t + cold by linarith)]
    obtain ⟨hl, hu⟩ := all_frequency_enclosure b r h w t (h0.trans_le ht').ne'
      cutoff N hcut hN hm hc P A hP a
    have hG : G N t ≤ allFrequencyTop b r cutoff t := hl
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hG)]
    exact (sub_le_iff_le_add'.2 hu).trans_lt he
  apply hconv.continuousOn
  exact (show ∀ᶠ N in atTop, ContinuousOn (G N) (Ici cold) from
    Eventually.of_forall fun N =>
      (continuous_const.max (frequency_spectrum_continuous b r h w cutoff N)).continuousOn).frequently

theorem all_frequency_crossing (b : Mesh p) (r : Realization p) (h : b.matches r)
    (w : ∀ i, 0 < dos b r i) (cutoff : ℕ)
    (hm : ∀ i j, r.modes i j = r.modes j i) (hc : ∀ i j, r.coulomb i j = r.coulomb j i)
    {cold hot : ℝ} (h0 : 0 < cold) (hord : cold ≤ hot)
    (hlo : 1 ≤ allFrequencyTop b r cutoff cold) (hhi : allFrequencyTop b r cutoff hot ≤ 1) :
    ∃ t ∈ Icc cold hot, allFrequencyTop b r cutoff t = 1 := by
  obtain ⟨t, ht, he⟩ := intermediate_value_Icc' hord
    ((all_frequency_continuous b r h w cutoff hm hc h0).mono fun _ ht => ht.1) ⟨hhi, hlo⟩
  exact ⟨t, ht, he⟩

end Grain.Pairing.Material
