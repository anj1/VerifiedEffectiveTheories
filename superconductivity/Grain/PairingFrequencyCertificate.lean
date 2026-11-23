import Grain.PairingFull

/-! Rational inputs for the infinite-frequency enclosure. -/

namespace Grain.Pairing.Material

open Finset

variable {p : Type} [Fintype p]

def profileBox (b : Mesh p) (i j : p) (t : ℚ) (k : ℕ) : Interval :=
  phononEnvelope (b.modes i j) ((2 * t * k)^2)

omit [Fintype p] in
theorem profile_enclosure (b : Mesh p) (r : Realization p) (h : b.matches r)
    (i j : p) (t : ℚ) (k : ℕ) : (profileBox b i j t k).contains (profile (r.modes i j) t k) := by
  simpa [profileBox, profile] using phonon_enclosure _ _ ((2 * t * k)^2) (sq_nonneg _)
    (h.2.1 i j)

def frequencyMetricBox (b : Mesh p) (t : ℚ) (a : p × Fin N) : Interval :=
  let normal := Interval.sum fun j : p =>
    (dosBox b j).mulPos ((profileBox b a.1 j t 0).add ((Interval.point 2).mulPos
      (Interval.sum fun k : Fin a.2.val => profileBox b a.1 j t (k.val + 1))))
  ((Interval.point (frequencyIndex a.2)).add normal).divPos (dosBox b a.1)

omit [Fintype p] in
private theorem profileBox_lo (b : Mesh p) (r : Realization p) (h : b.matches r)
    (i j : p) (t : ℚ) (k : ℕ) : 0 ≤ (profileBox b i j t k).lo := by
  unfold profileBox phononEnvelope
  generalize h.2.1 i j = hh
  generalize b.modes i j = boxes at hh ⊢
  generalize r.modes i j = modes at hh
  induction hh with
  | nil => exact le_rfl
  | @cons box mode _ _ hm _ ih =>
    have he := hm.1.le
    have hg := hm.2.1
    exact add_nonneg (div_nonneg (by change 0 ≤ 2 * box.energy.lo * box.vertexSq.lo; positivity)
      (by change 0 ≤ box.energy.hi * box.energy.hi + (2 * t * k)^2
          exact add_nonneg (mul_self_nonneg _) (sq_nonneg _))) ih

theorem frequency_metric_enclosure (b : Mesh p) (r : Realization p) (h : b.matches r)
    (hw : 0 < b.halfWidth) (hd : ∀ i, 0 < (dosBox b i).lo) (t : ℚ) (a : p × Fin N) :
    (frequencyMetricBox b t a).contains (frequencyMetric b r t a) := by
  have w (i : p) : (dosBox b i).contains (dos b r i) := dos_enclosure b r h hw i
  let B (j : p) := (profileBox b a.1 j t 0).add ((Interval.point 2).mulPos
    (Interval.sum fun k : Fin a.2.val => profileBox b a.1 j t (k.val + 1)))
  have hB (j : p) : 0 ≤ (B j).lo := add_nonneg (profileBox_lo b r h _ _ _ _)
    (mul_nonneg (by norm_num [Interval.point]) (sum_nonneg fun _ _ => profileBox_lo b r h _ _ _ _))
  unfold frequencyMetricBox frequencyMetric fullMetric
  apply Interval.div_contains _ (hd _) _ (w _)
  · exact add_nonneg (by unfold frequencyIndex Interval.point; positivity)
      (sum_nonneg fun j _ => mul_nonneg (hd j).le (hB j))
  · have hfreq : ((frequencyIndex a.2 : ℚ) : ℝ) = 2 * (a.2.val : ℝ) + 1 := by
      simp [frequencyIndex]
    rw [← hfreq]
    apply Interval.add_contains (Interval.point_contains _)
    apply Interval.sum_contains
    intro j
    apply Interval.mul_contains (hd j).le (hB j) (w j)
    apply Interval.add_contains (profile_enclosure b r h _ _ _ _)
    rw [← Fin.sum_univ_eq_sum_range (fun k => profile (r.modes a.1 j) t (k + 1))]
    apply Interval.mul_contains (a := Interval.point 2) (by decide)
      (sum_nonneg fun _ _ => profileBox_lo b r h _ _ _ _) (Interval.point_contains 2)
    exact Interval.sum_contains _ _ fun k => profile_enclosure b r h _ _ _ _

private def momentBox (boxes : List ModeBox) : Interval :=
  Interval.sumList (boxes.map fun m => ((Interval.point 2).mulPos m.energy).mulPos m.vertexSq)

def decayUpper (b : Mesh p) (t : ℚ) (i j : p) : ℚ :=
  (momentBox (b.modes i j)).hi / (4*t^2)

omit [Fintype p] in
theorem decay_upper (b : Mesh p) (r : Realization p) (h : b.matches r) (t : ℚ) (i j : p) :
    profileMoment (r.modes i j) / (4*(t : ℝ)^2) ≤ decayUpper b t i j := by
  have hh (boxes modes) (h : List.Forall₂ ModeBox.matches boxes modes) :
      (momentBox boxes).contains (profileMoment modes) := by
    apply Interval.sumList_contains
    induction h with
    | nil => exact .nil
    | @cons box mode _ _ hm _ ih =>
      exact .cons (Interval.mul_contains (by
        change 0 ≤ 2 * box.energy.lo
        exact mul_nonneg (by decide) hm.1.le) hm.2.1
        (Interval.mul_contains (a := Interval.point 2) (by decide) hm.1.le
          (Interval.point_contains 2) hm.2.2.1) hm.2.2.2) ih
  simp only [decayUpper, Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat]
  exact div_le_div_of_nonneg_right (hh _ _ (h.2.1 i j)).2 (by positivity)

def zeroTransferUpper (b : Mesh p) (t : ℚ) (i j : p) : ℚ :=
  (profileBox b i j t 0).hi

def retainedAllowanceQ (b : Mesh p) (t : ℚ) (a : p × Fin N) : ℚ :=
  ∑ j, (2 * decayUpper b t a.1 j / ((N - a.2.val : ℕ) : ℚ) +
    2 * decayUpper b t a.1 j / ((a.2.val + N + 1 : ℕ) : ℚ))

def discardedAllowanceQ (b : Mesh p) (t : ℚ) (i : p) : ℚ :=
  ∑ j, (zeroTransferUpper b t i j + 4 * decayUpper b t i j)

/-- A sufficient rational upper certificate at a given temperature.
The retained rows include the extra coupling to the omitted
frequencies. The complement uses its smallest bare metric entry. -/
theorem all_frequency_upper_rows (b : Mesh p) (r : Realization p) (h : b.matches r)
    (hw : 0 < b.halfWidth) (hd : ∀ i, 0 < (dosBox b i).lo)
    (hm : ∀ i j, r.modes i j = r.modes j i) (hc : ∀ i j, r.coulomb i j = r.coulomb j i)
    (t : ℚ) (ht : 0 < t) (cutoff N : ℕ) (hcut : cutoff ≤ N) (u : ℚ) (hu : 0 ≤ u)
    (hhead : ∀ a : p × Fin N, (∑ j : p × Fin N, (kernelBox b cutoff t a j).radius 0) +
      retainedAllowanceQ b t a ≤ u * (frequencyMetricBox b t a).lo)
    (htail : ∀ i : p, discardedAllowanceQ b t i ≤ u * ((2 * (N : ℚ) + 1) / (dosBox b i).hi)) :
    allFrequencyTop b r cutoff t ≤ (u : ℝ) := by
  have hwgt (i : p) := dos_enclosure b r h hw i
  have w (i : p) : 0 < dos b r i := (by exact_mod_cast (hd i) : (0 : ℝ) < (dosBox b i).lo).trans_le
    (hwgt i).1
  have hu' : (0 : ℝ) ≤ u := by exact_mod_cast hu
  refine all_frequency_upper b r cutoff _ N hu' fun e =>
    all_grids_upper b r h w _ (by exact_mod_cast ht.ne') cutoff N hcut hm hc
      (fun i j => zeroTransferUpper b t i j) (fun i j => decayUpper b t i j)
      (fun i j => (profile_enclosure b r h i j t 0).2) (decay_upper b r h t)
      u hu' ?_ ?_ e
  · intro x
    have hf := (le_abs_self (realForm (meshKernel r cutoff t) x)).trans
      (realForm_abs_le_row _ (mesh_kernel_symm r cutoff t hm hc) x)
    apply (add_le_add_left hf _).trans
    unfold realMetric
    rw [← sum_add_distrib, mul_sum]
    apply sum_le_sum
    intro a _
    rw [← add_mul, ← mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    have hb : (∑ j : p × Fin N, |meshKernel r cutoff t a j|) ≤
        ∑ j : p × Fin N, ((kernelBox b cutoff t a j).radius 0 : ℝ) := by
      apply sum_le_sum
      intro j _
      simpa using Interval.abs_sub_le_radius (kernel_enclosure b r h cutoff t a j) 0
    refine (add_le_add_left hb _).trans ?_
    have hh := hhead a
    rw [← Rat.cast_le (K := ℝ)] at hh
    unfold retainedAllowanceQ at hh
    push_cast at hh
    unfold retainedAllowance
    push_cast
    exact hh.trans (mul_le_mul_of_nonneg_left (frequency_metric_enclosure b r h hw hd t a).1 hu')
  · intro i
    have hh := htail i
    rw [← Rat.cast_le (K := ℝ)] at hh
    unfold discardedAllowanceQ at hh
    push_cast at hh
    exact hh.trans (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_left (by positivity) (w i) (hwgt i).2) hu')

/-- A single retained trial gives a lower bound on the all-frequency
spectrum when evaluated with the full normal metric. -/
theorem all_frequency_lower_trial (b : Mesh p) (r : Realization p) (h : b.matches r)
    (hw : 0 < b.halfWidth) (hd : ∀ i, 0 < (dosBox b i).lo)
    (hm : ∀ i j, r.modes i j = r.modes j i) (hc : ∀ i j, r.coulomb i j = r.coulomb j i)
    (t : ℚ) (ht : 0 < t) (cutoff N : ℕ) (hcut : cutoff ≤ N) (hN : 0 < N)
    (l : ℚ) (x : p × Fin N → ℚ)
    (hx : trialTest (kernelBox b cutoff t) (frequencyMetricBox b t) l x) :
    (l : ℝ) ≤ allFrequencyTop b r cutoff t := by
  have w (i : p) : 0 < dos b r i := (by exact_mod_cast (hd i) : (0 : ℝ) < (dosBox b i).lo).trans_le
    (dos_enclosure b r h hw i).1
  have hf := trial_enclosure _ _ l x _ _ (kernel_enclosure b r h cutoff t)
    (frequency_metric_enclosure b r h hw hd t) hx
  have he := form_le_spectrum (meshKernel r cutoff t) (frequencyMetric b r t)
    (frequencyMetric_pos b r h w t) (fun a => (x a : ℝ))
  have hl := le_of_mul_le_mul_right (hf.2.trans he) hf.1
  exact hl.trans ((le_max_right _ _).trans (all_frequency_enclosure b r h w t
    (by exact_mod_cast ht.ne') cutoff N hcut hN hm hc
    (fun i j => zeroTransferUpper b t i j) (fun i j => decayUpper b t i j)
    (fun i j => (profile_enclosure b r h i j t 0).2) (decay_upper b r h t)).1)

end Grain.Pairing.Material
