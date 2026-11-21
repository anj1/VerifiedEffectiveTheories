import Grain.BCSCertificate
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Trace of a finite matrix exponential, with a geometric bound on the
tail of its entire power series. -/

namespace Grain.ThermalTrace

open Matrix

noncomputable def partition {s : Type} [Fintype s] [DecidableEq s] (A : Matrix s s ℝ) : ℝ :=
  ∑' k : ℕ, (A ^ k).trace / k.factorial

private theorem power_rows {s : Type} [Fintype s] [DecidableEq s]
    (A : Matrix s s ℝ) {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ i, ∑ j, |A i j| ≤ r) :
    ∀ k i, ∑ j, |(A ^ k) i j| ≤ r ^ k := by
  intro k
  induction k with
  | zero =>
    intro i
    simp [Matrix.one_apply, apply_ite abs]
  | succ k ih =>
    intro i
    rw [pow_succ']
    calc
      (∑ j, |(A * A ^ k) i j|) ≤ ∑ j, ∑ l, |A i l| * |(A ^ k) l j| := by
        apply Finset.sum_le_sum
        intro j _
        simpa only [Matrix.mul_apply, abs_mul] using
          (Finset.abs_sum_le_sum_abs (fun l => A i l * (A ^ k) l j) Finset.univ)
      _ = ∑ l, |A i l| * ∑ j, |(A ^ k) l j| := by
        rw [Finset.sum_comm]
        simp_rw [Finset.mul_sum]
      _ ≤ r ^ k * r := by
        calc
          _ ≤ ∑ l, |A i l| * r ^ k :=
            Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (ih l) (abs_nonneg _)
          _ = r ^ k * (∑ l, |A i l|) := by
            simp_rw [mul_comm (|A i _|) (r ^ k)]
            rw [Finset.mul_sum]
          _ ≤ _ := mul_le_mul_of_nonneg_left (h i) (pow_nonneg hr _)
      _ = r ^ (k + 1) := (pow_succ _ _).symm

private theorem trace_term_bound {s : Type} [Fintype s] [DecidableEq s]
    (A : Matrix s s ℝ) {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ i, ∑ j, |A i j| ≤ r) (k : ℕ) :
    |(A ^ k).trace / (k.factorial : ℝ)| ≤ Fintype.card s * r ^ k / k.factorial := by
  rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ k.factorial)]
  gcongr
  unfold Matrix.trace
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    (∑ i, |(A ^ k) i i|) ≤ ∑ i : s, r ^ k := by
      apply Finset.sum_le_sum
      intro i _
      exact (Finset.single_le_sum (fun j _ => abs_nonneg ((A ^ k) i j))
        (Finset.mem_univ i)).trans (power_rows A hr h k i)
    _ = _ := by simp

private theorem tail_majorant {r : ℝ} (hr : 0 ≤ r) (n i : ℕ) :
    r ^ (i + n) / ((i + n).factorial : ℝ) ≤
      (r ^ n / (n.factorial : ℝ)) * (r / (n + 1 : ℝ)) ^ i := by
  rw [add_comm i n, pow_add, div_pow, div_mul_div_comm]
  have hf : (n.factorial : ℝ) * (n + 1 : ℝ)^i ≤ ((n + i).factorial : ℝ) := by
    exact_mod_cast (Nat.factorial_mul_pow_le_factorial (m := n) (n := i))
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) hf

theorem partition_enclosure {s : Type} [Fintype s] [DecidableEq s]
    (A : Matrix s s ℝ) {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ i, ∑ j, |A i j| ≤ r) (n : ℕ) (hn : r / (n + 1 : ℝ) ≤ 1 / 2) :
    |partition A - ∑ k ∈ Finset.range n, (A ^ k).trace / (k.factorial : ℝ)| ≤
      2 * Fintype.card s * r ^ n / n.factorial := by
  let f (k : ℕ) := (A ^ k).trace / (k.factorial : ℝ)
  let c : ℝ := Fintype.card s * r ^ n / n.factorial
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hm (i : ℕ) : ‖f (i + n)‖ ≤ c * (1/2 : ℝ)^i := by
    rw [Real.norm_eq_abs]
    apply (trace_term_bound A hr h _).trans
    rw [mul_div_assoc]
    have he := tail_majorant hr n i
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ r / (n + 1 : ℝ)) hn i
    have hz := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ r ^ n / (n.factorial : ℝ))
    simpa only [c, mul_div_assoc, mul_assoc] using
      mul_le_mul_of_nonneg_left (he.trans hz) (by positivity : (0 : ℝ) ≤ Fintype.card s)
  have hg := (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ) < 1)).mul_left c
  have hs : Summable fun i => ‖f (i+n)‖ := hg.of_nonneg_of_le (fun _ => norm_nonneg _) hm
  have hf : Summable f := (summable_nat_add_iff n).mp hs.of_norm
  change |(∑' k, f k) - ∑ k ∈ Finset.range n, f k| ≤ _
  rw [← hf.sum_add_tsum_nat_add n, add_sub_cancel_left, ← Real.norm_eq_abs]
  apply (norm_tsum_le_tsum_norm hs).trans
  apply (hs.tsum_le_tsum hm hg).trans
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  dsimp [c]
  ring_nf
  norm_num

/-- Compare the partition ratio with exponentials of proposed response
endpoints, avoiding a separate numerical implementation of the logarithm. -/
theorem response_enclosure {t a b l u zl zu wl wu : ℝ}
    (ht : 0 < t) (hz : 0 < zl) (ha : zl ≤ a ∧ a ≤ zu) (hb : wl ≤ b ∧ b ≤ wu)
    (hl : Real.exp (l / (200 * t)) * zu ≤ wl)
    (hu : wu ≤ Real.exp (u / (200 * t)) * zl) :
    l ≤ 200 * t * Real.log (b / a) ∧ 200 * t * Real.log (b / a) ≤ u := by
  have az := hz.trans_le ha.1
  have d : 0 < 200 * t := by positivity
  have lower : Real.exp (l / (200 * t)) ≤ b / a :=
    (le_div_iff₀ az).2 ((mul_le_mul_of_nonneg_left ha.2 (Real.exp_nonneg _)).trans
      (hl.trans hb.1))
  have upper : b / a ≤ Real.exp (u / (200 * t)) :=
    (div_le_iff₀ az).2 (hb.2.trans (hu.trans
      (mul_le_mul_of_nonneg_left ha.1 (Real.exp_nonneg _))))
  have h₁ := Real.log_le_log (Real.exp_pos _) lower
  have h₂ := Real.log_le_log ((Real.exp_pos _).trans_le lower) upper
  rw [Real.log_exp] at h₁ h₂
  exact ⟨by simpa [mul_comm (200 * t)] using (div_le_iff₀ d).1 h₁,
    by simpa [mul_comm (200 * t)] using (le_div_iff₀ d).1 h₂⟩

end Grain.ThermalTrace
