import Grain.PairingParent

/-! The exact static pairing response in a spectral representation.
The bound is uniform in the number of oscillator levels retained. -/

namespace Grain.HarmonicBand

open Phonon

variable {n c m : ℕ}

/-- The uncoupled oscillator form on an occupation box. -/
noncomputable def oscillatorForm {cutoff : ℕ} (d : Input n c m)
    (ψ : Quanta m cutoff → State n → ℝ) : ℝ :=
  ∑ q, ∑ k, frequency d k * normSq (annihilate k ψ q)

/-- A cutoff-independent comparison that retains half of the positive
oscillator form. The same electronic remainder bounds both sides. -/
theorem harmonic_oscillator_comparison {cutoff : ℕ}
    (d : Input n c m) (h : Valid d) (ψ : Quanta m cutoff → State n → ℝ) :
    let electronicEnergy := ∑ q, form (electronic d) (ψ q)
    let remainder := ∑ q, ∑ k,
      normSq (act (electronPhonon d k) (ψ q)) / (d.force k : ℝ)
    |harmonicForm d ψ - electronicEnergy - oscillatorForm d ψ| ≤
      oscillatorForm d ψ / 2 + remainder := by
  intro electronicEnergy remainder
  let lowered q k := annihilate k ψ q
  let vertex q k := act (electronPhonon d k) (ψ q)
  have bound (q : Quanta m cutoff) (k : Fin m) :
      |2 * coupling d k * inner (lowered q k) (vertex q k)| ≤
        frequency d k * normSq (lowered q k) / 2 +
          normSq (vertex q k) / (d.force k : ℝ) := by
    let ω := frequency d k
    let g := coupling d k
    have hω : 0 < ω := frequency_pos d h k
    have he : (ω / 2) * (2 * g / ω)^2 = 1 / (d.force k : ℝ) := by
      have hd := displacement_coefficient d h k
      change ω * (g / ω)^2 = _ at hd
      rw [show (ω / 2) * (2 * g / ω)^2 = 2 * (ω * (g / ω)^2) by ring, hd]
      ring
    have hc (s : ℝ) : 2 * (ω / 2) * (s * (2 * g / ω)) = s * (2 * g) := by
      field_simp [hω.ne']
    have hnon (s : ℝ) (hs : s = 1 ∨ s = -1) :
        0 ≤ ω * normSq (lowered q k) / 2 +
          s * (2 * g * inner (lowered q k) (vertex q k)) +
          normSq (vertex q k) / (d.force k : ℝ) := by
      have hz := mul_nonneg (show 0 ≤ ω / 2 by positivity)
        (normSq_nonneg (fun i => lowered q k i + s * (2 * g / ω) * vertex q k i))
      rw [complete_square] at hz
      have hsquare : s ^ 2 = 1 := by rcases hs with rfl | rfl <;> norm_num
      calc
        0 ≤ _ := hz
        _ = ω * normSq (lowered q k) / 2 +
              (2 * (ω / 2) * (s * (2 * g / ω))) * inner (lowered q k) (vertex q k) +
              (s ^ 2 * ((ω / 2) * (2 * g / ω)^2)) * normSq (vertex q k) := by ring
        _ = _ := by rw [hc, hsquare, one_mul, he]; ring
    exact abs_le.mpr ⟨by linarith only [hnon 1 (Or.inl rfl)],
      by linarith only [hnon (-1) (Or.inr rfl)]⟩
  have he : harmonicForm d ψ - electronicEnergy - oscillatorForm d ψ =
      ∑ q, ∑ k, 2 * coupling d k * inner (lowered q k) (vertex q k) := by
    simp only [harmonicForm, electronicEnergy, oscillatorForm, lowered, vertex, Finset.sum_add_distrib]
    ring
  rw [he]
  calc
    _ ≤ ∑ q, ∑ k, |2 * coupling d k * inner (lowered q k) (vertex q k)| :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun _ _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ q, ∑ k, (frequency d k * normSq (lowered q k) / 2 +
          normSq (vertex q k) / (d.force k : ℝ)) :=
      Finset.sum_le_sum fun q _ => Finset.sum_le_sum fun k _ => bound q k
    _ = _ := by
      simp only [remainder, oscillatorForm, lowered, vertex, Finset.sum_add_distrib, Finset.sum_div]

end Grain.HarmonicBand

namespace Grain.Pairing.ParentResponse

open Finset Set

noncomputable def gibbsFactor (β E : ℝ) : ℝ := Real.exp (-β * E)

/-- Imaginary-time weight of a transition, with time rescaled to [0,1].
The integral includes degenerate transitions without a divided difference. -/
noncomputable def transitionWeight (β E F : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1, Real.exp ((1 - s) * (-β * E) + s * (-β * F))

private theorem interpolant_continuous (β E F : ℝ) :
    Continuous (fun s : ℝ => Real.exp ((1 - s) * (-β * E) + s * (-β * F))) := by
  fun_prop

private theorem chord_integral (a b : ℝ) :
    (∫ s in (0 : ℝ)..1, (1 - s) * a + s * b) = (a + b) / 2 := by
  have h : (fun s : ℝ => (1 - s) * a + s * b) = fun s => a + (b - a) * s := by
    funext s
    ring
  have hc : Continuous (fun s : ℝ => (b - a) * s) := by fun_prop
  rw [h, intervalIntegral.integral_add (continuous_const.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id]
  norm_num
  ring

private theorem chord_bound (x y : ℝ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    Real.exp ((1 - s) * x + s * y) ≤ (1 - s) * Real.exp x + s * Real.exp y := by
  simpa only [smul_eq_mul] using convexOn_exp.2 (mem_univ x) (mem_univ y)
    (sub_nonneg.mpr hs.2) hs.1 (show 1 - s + s = 1 by ring)

theorem transition_weight_bounds (β E F : ℝ) :
    0 ≤ transitionWeight β E F ∧
      transitionWeight β E F ≤ (gibbsFactor β E + gibbsFactor β F) / 2 := by
  unfold transitionWeight
  constructor
  · exact intervalIntegral.integral_nonneg (by norm_num) fun _ _ => Real.exp_nonneg _
  · rw [← chord_integral, gibbsFactor, gibbsFactor]
    have hc : Continuous (fun s : ℝ => (1 - s) * Real.exp (-β * E) +
        s * Real.exp (-β * F)) := by fun_prop
    exact intervalIntegral.integral_mono_on (by norm_num)
      ((interpolant_continuous β E F).intervalIntegrable _ _) (hc.intervalIntegrable _ _)
      (fun _ hs => chord_bound _ _ hs)

theorem transition_weight_pos (β E F : ℝ) : 0 < transitionWeight β E F := by
  let a := min (-β * E) (-β * F)
  have h : Real.exp a ≤ transitionWeight β E F := by
    unfold transitionWeight
    have hm : (∫ _ : ℝ in (0 : ℝ)..1, Real.exp a) = Real.exp a := by
      simp
    rw [← hm]
    refine intervalIntegral.integral_mono_on (by norm_num)
      (continuous_const.intervalIntegrable _ _) ((interpolant_continuous β E F).intervalIntegrable _ _)
      fun s hs => Real.exp_le_exp.mpr ?_
    have h₁ := mul_le_mul_of_nonneg_left (min_le_left (-β * E) (-β * F)) (sub_nonneg.mpr hs.2)
    have h₂ := mul_le_mul_of_nonneg_left (min_le_right (-β * E) (-β * F)) hs.1
    linarith only [h₁, h₂]
  exact (Real.exp_pos _).trans_le h

theorem transition_weight_self (β E : ℝ) :
    transitionWeight β E E = gibbsFactor β E := by
  unfold transitionWeight gibbsFactor
  simp only [show ∀ s : ℝ, (1 - s) * (-β * E) + s * (-β * E) = -β * E from fun s => by ring]
  simp

/-- Positive harmonic frequencies give a summable product of geometric
Boltzmann factors, with every occupation included. -/
theorem oscillator_gibbs_summable (m : ℕ) (a : Fin m → ℝ) (ha : ∀ k, 0 < a k) :
    Summable fun q : Fin m → ℕ => Real.exp (-(∑ k, a k * (q k : ℝ))) := by
  induction m with
  | zero => exact Summable.of_finite
  | succ m ih =>
    let e := Fin.consEquiv (fun _ : Fin (m + 1) => ℕ)
    refine e.summable_iff.mp ?_
    have ht := ih (fun k => a k.succ) (fun k => ha k.succ)
    have hg : Summable fun n : ℕ => Real.exp (-(a 0 * (n : ℝ))) := by
      have hr : Real.exp (-(a 0)) < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos (ha 0))
      convert summable_geometric_of_lt_one (Real.exp_nonneg (-(a 0))) hr using 1
      funext n
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have hf (q : ℕ × (Fin m → ℕ)) :
        (∑ k, a k * ((e q k : ℕ) : ℝ)) = a 0 * (q.1 : ℝ) +
          ∑ k : Fin m, a k.succ * (q.2 k : ℝ) := by
      rw [Fin.sum_univ_succ]
      simp [e]
    change Summable fun q : ℕ × (Fin m → ℕ) => Real.exp (-(∑ k, a k * ((e q k : ℕ) : ℝ)))
    simp only [hf, neg_add_rev, Real.exp_add]
    let g (q : Fin m → ℕ) := Real.exp (-(∑ k : Fin m, a k.succ * (q k : ℝ)))
    let f (j : ℕ) := Real.exp (-(a 0 * (j : ℝ)))
    change Summable (fun q : ℕ × (Fin m → ℕ) => g q.2 * f q.1)
    apply (summable_prod_of_nonneg (fun q : ℕ × (Fin m → ℕ) =>
      mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _) :
        0 ≤ fun q : ℕ × (Fin m → ℕ) => g q.2 * f q.1)).2
    refine ⟨fun j => ht.mul_right (f j), ?_⟩
    simp_rw [tsum_mul_right]
    exact hg.mul_left (∑' q, g q)

/-- The min–max eigenvalue comparison with half of the oscillator form
implies the trace-class premise of the exact response bound. The labels
may be assigned after sorting the oscillator energies with multiplicity. -/
theorem harmonic_gibbs_summable {n c m : ℕ} (d : HarmonicBand.Input n c m)
    (h : HarmonicBand.Valid d) (β : ℝ) (hβ : 0 < β) (C : ℝ)
    (E : HarmonicBand.State n × (Fin m → ℕ) → ℝ)
    (hE : ∀ i, (∑ k, HarmonicBand.frequency d k * (i.2 k : ℝ)) / 2 - C ≤ E i) :
    Summable fun i => gibbsFactor β (E i) := by
  let a (k : Fin m) := β * HarmonicBand.frequency d k / 2
  have ha (k : Fin m) : 0 < a k :=
    div_pos (mul_pos hβ (HarmonicBand.frequency_pos d h k)) (by norm_num)
  have hg := oscillator_gibbs_summable m a ha
  have hc : Summable fun q : Fin m → ℕ => Real.exp (β * C) *
      Real.exp (-(∑ k, a k * (q k : ℝ))) := hg.mul_left _
  refine Summable.of_nonneg_of_le
    (f := fun i : HarmonicBand.State n × (Fin m → ℕ) =>
      Real.exp (β * C) * Real.exp (-(∑ k, a k * (i.2 k : ℝ))))
    (fun _ => Real.exp_nonneg _) (fun i => ?_) ?_
  · rw [gibbsFactor, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have he : ∑ k, a k * (i.2 k : ℝ) =
        β * ((∑ k, HarmonicBand.frequency d k * (i.2 k : ℝ)) / 2) := by
      simp only [a, mul_div_assoc, mul_sum, sum_div]
      apply sum_congr rfl
      intro k _
      ring
    rw [he]
    nlinarith only [mul_le_mul_of_nonneg_left (hE i) hβ.le]
  · apply (summable_prod_of_nonneg (fun _ => mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))).2
    exact ⟨fun _ => hc, Summable.of_finite⟩

variable {ι : Type}

/-- The numerator of the static Lehmann response on a finite set of
eigenstates. A real symmetric source has weights A(i,j)^2. -/
noncomputable def responseSum (β : ℝ) (E : ι → ℝ) (A : ι → ι → ℝ) (S : Finset ι) : ℝ :=
  ∑ i ∈ S, ∑ j ∈ S, transitionWeight β (E i) (E j) * A i j ^ 2

private theorem response_sum_nonneg (β : ℝ) (E : ι → ℝ) (A : ι → ι → ℝ) (S : Finset ι) :
    0 ≤ responseSum β E A S :=
  sum_nonneg fun i _ => sum_nonneg fun j _ =>
    mul_nonneg (transition_weight_bounds β (E i) (E j)).1 (sq_nonneg _)

theorem response_sum_le (β : ℝ) (E : ι → ℝ) (A : ι → ι → ℝ)
    (hA : ∀ i j, A i j = A j i) (S : Finset ι) (M : ℝ)
    (hM : ∀ i ∈ S, ∑ j ∈ S, A i j ^ 2 ≤ M) :
    responseSum β E A S ≤ M * ∑ i ∈ S, gibbsFactor β (E i) := by
  let w (i : ι) := gibbsFactor β (E i)
  have hw (i : ι) : 0 ≤ w i := Real.exp_nonneg _
  let g (i j : ι) := w i / 2 * A i j ^ 2
  calc
    _ ≤ ∑ i ∈ S, ∑ j ∈ S, ((w i + w j) / 2) * A i j ^ 2 :=
      sum_le_sum fun i _ => sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_right (transition_weight_bounds β (E i) (E j)).2 (sq_nonneg _)
    _ = ∑ i ∈ S, ∑ j ∈ S, (g i j + g j i) := by
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      dsimp [g]
      rw [← hA i j]
      ring
    _ = ∑ i ∈ S, w i * ∑ j ∈ S, A i j ^ 2 := by
      simp only [sum_add_distrib]
      conv_rhs =>
        simp only [mul_sum]
      rw [sum_comm (f := fun i j => g j i)]
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro i _
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro j _
      dsimp [g]
      ring
    _ ≤ _ := by
      rw [mul_sum]
      exact sum_le_sum fun i hi => by
        rw [mul_comm M]
        exact mul_le_mul_of_nonneg_left (hM i hi) (hw i)

/-- Full zero-mean static susceptibility. The nonnegative Lehmann series
is summed by the supremum of finite principal sums. Every finite set of
transitions lies in a principal sum. -/
noncomputable def susceptibility (β : ℝ) (E : ι → ℝ) (A : ι → ι → ℝ) : ℝ :=
  (β / ∑' i, gibbsFactor β (E i)) * sSup (range (responseSum β E A))

/-- A bounded source in a trace-class Gibbs state has no positive-temperature
susceptibility pole. M bounds the square of the source norm. The estimate
also covers a countably infinite oscillator spectrum. -/
theorem susceptibility_bounds [Nonempty ι] (β : ℝ) (hβ : 0 ≤ β)
    (E : ι → ℝ) (A : ι → ι → ℝ) (hA : ∀ i j, A i j = A j i)
    (hZ : Summable fun i => gibbsFactor β (E i)) (M : ℝ) (hM : 0 ≤ M)
    (hrows : ∀ (S : Finset ι) (i : ι), ∑ j ∈ S, A i j ^ 2 ≤ M) :
    0 ≤ susceptibility β E A ∧ susceptibility β E A ≤ β * M := by
  let Z := ∑' i, gibbsFactor β (E i)
  have hz : 0 < Z := (Real.exp_pos _).trans_le
    (hZ.le_tsum (Classical.arbitrary ι) (fun _ _ => Real.exp_nonneg _))
  have hs (S : Finset ι) : responseSum β E A S ≤ M * Z :=
    (response_sum_le β E A hA S M (fun i _ => hrows S i)).trans
      (mul_le_mul_of_nonneg_left (hZ.sum_le_tsum S (fun _ _ => Real.exp_nonneg _)) hM)
  have hbd : BddAbove (range (responseSum β E A)) := ⟨M * Z, by rintro _ ⟨S, rfl⟩; exact hs S⟩
  have hnon : (range (responseSum β E A)).Nonempty := ⟨_, mem_range_self ∅⟩
  have hsup' : sSup (range (responseSum β E A)) ≤ M * Z :=
    csSup_le hnon (by rintro _ ⟨S, rfl⟩; exact hs S)
  unfold susceptibility
  change 0 ≤ (β / Z) * _ ∧ (β / Z) * _ ≤ β * M
  constructor
  · exact mul_nonneg (div_nonneg hβ hz.le)
      ((response_sum_nonneg β E A ∅).trans (le_csSup hbd (mem_range_self ∅)))
  · calc
      _ ≤ (β / Z) * (M * Z) := mul_le_mul_of_nonneg_left hsup' (div_nonneg hβ hz.le)
      _ = _ := by field_simp

/-- When a source has a nonzero transition, its inverse static response
is bounded away from zero at every finite positive inverse temperature. -/
theorem inverse_susceptibility_lower [Nonempty ι] (β : ℝ) (hβ : 0 < β)
    (E : ι → ℝ) (A : ι → ι → ℝ) (hA : ∀ i j, A i j = A j i)
    (hZ : Summable fun i => gibbsFactor β (E i)) (M : ℝ) (hM : 0 < M)
    (hrows : ∀ (S : Finset ι) (i : ι), ∑ j ∈ S, A i j ^ 2 ≤ M)
    {i j : ι} (hn : A i j ≠ 0) :
    (β * M)⁻¹ ≤ (susceptibility β E A)⁻¹ := by
  classical
  let Z := ∑' i, gibbsFactor β (E i)
  have hz : 0 < Z := (Real.exp_pos _).trans_le
    (hZ.le_tsum i (fun _ _ => Real.exp_nonneg _))
  have hbd : BddAbove (range (responseSum β E A)) := by
    refine ⟨M * Z, ?_⟩
    rintro _ ⟨S, rfl⟩
    exact (response_sum_le β E A hA S M fun i _ => hrows S i).trans
      (mul_le_mul_of_nonneg_left (hZ.sum_le_tsum S (fun _ _ => Real.exp_nonneg _)) hM.le)
  let S : Finset ι := {i, j}
  have hr : 0 < responseSum β E A S := by
    refine sum_pos' (fun a _ => sum_nonneg fun b _ =>
      mul_nonneg (transition_weight_bounds β (E a) (E b)).1 (sq_nonneg _)) ?_
    refine ⟨i, by simp [S], sum_pos' (fun b _ =>
      mul_nonneg (transition_weight_bounds β (E i) (E b)).1 (sq_nonneg _)) ?_⟩
    exact ⟨j, by simp [S], mul_pos (transition_weight_pos β (E i) (E j)) (sq_pos_of_ne_zero hn)⟩
  have hp : 0 < susceptibility β E A :=
    mul_pos (div_pos hβ hz) (hr.trans_le (le_csSup hbd (mem_range_self S)))
  exact inv_anti₀ hp (susceptibility_bounds β hβ.le E A hA hZ M hM.le hrows).2

/-- In the pairing certificate's temperature units, a source with norm
at most sqrt(n) has inverse response at least τ/(π n). The spectrum may
contain all oscillator occupations. -/
theorem harmonic_inverse_response_lower {n c m : ℕ} (d : HarmonicBand.Input n c m)
    (h : HarmonicBand.Valid d) (τ : ℝ) (hτ : 0 < τ) (C : ℝ)
    (E : HarmonicBand.State n × (Fin m → ℕ) → ℝ)
    (hE : ∀ a, (∑ k, HarmonicBand.frequency d k * (a.2 k : ℝ)) / 2 - C ≤ E a)
    (A : (HarmonicBand.State n × (Fin m → ℕ)) → (HarmonicBand.State n × (Fin m → ℕ)) → ℝ)
    (hA : ∀ i j, A i j = A j i)
    (hrows : ∀ (S : Finset (HarmonicBand.State n × (Fin m → ℕ))) i,
      ∑ j ∈ S, A i j ^ 2 ≤ n) {i j} (hn : A i j ≠ 0) :
    τ / (Real.pi * n) ≤ (susceptibility (Real.pi / τ) E A)⁻¹ := by
  have hβ := div_pos Real.pi_pos hτ
  have hnp : 0 < (n : ℝ) := by exact_mod_cast h.1
  have hb := inverse_susceptibility_lower _ hβ E A hA
    (harmonic_gibbs_summable d h _ hβ C E hE) n hnp hrows hn
  convert hb using 1
  field_simp [Real.pi_pos.ne', hτ.ne', hnp.ne']

private theorem response_sum_mono (β : ℝ) (E : ι → ℝ) (A : ι → ι → ℝ)
    {S T : Finset ι} (h : S ⊆ T) : responseSum β E A S ≤ responseSum β E A T :=
  (sum_le_sum_of_subset_of_nonneg h (fun i _ _ => sum_nonneg fun j _ =>
    mul_nonneg (transition_weight_bounds β (E i) (E j)).1 (sq_nonneg _))).trans
      (sum_le_sum fun i _ => sum_le_sum_of_subset_of_nonneg h
        (fun j _ _ => mul_nonneg (transition_weight_bounds β (E i) (E j)).1 (sq_nonneg _)))

theorem susceptibility_fintype [Fintype ι] (β : ℝ) (E : ι → ℝ) (A : ι → ι → ℝ) :
    susceptibility β E A = (β / ∑ i, gibbsFactor β (E i)) * responseSum β E A Finset.univ := by
  rw [susceptibility, tsum_fintype]
  congr 1
  have hb : ∀ y ∈ range (responseSum β E A), y ≤ responseSum β E A Finset.univ := by
    rintro _ ⟨S, rfl⟩
    exact response_sum_mono β E A (subset_univ S)
  exact le_antisymm (csSup_le ⟨_, mem_range_self Finset.univ⟩ hb)
    (le_csSup ⟨_, hb⟩ (mem_range_self Finset.univ))

end Grain.Pairing.ParentResponse
