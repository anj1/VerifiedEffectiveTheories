import Grain.PairingFrequency

/-! Error transfer at the instability threshold. An electronic parent
calculation can supply residuals from vertex and projection terms in
the same units as the shifted pairing pencil F - D. -/

namespace Grain.Pairing.Material

open Finset Set

variable {ι : Type} [Fintype ι]

/-- Add the absolute row budget of the interaction residual and the
diagonal budget of the normal-state residual. Testing the pencil at
one permits both errors to be measured in a common metric. -/
theorem threshold_form_error (F G : ι → ι → ℝ) (D E W : ι → ℝ)
    (ε : ℝ) (hs : ∀ i j, F i j - G i j = F j i - G j i)
    (hrow : ∀ i, (∑ j, |F i j - G i j|) + |D i - E i| ≤ ε * W i)
    (x : ι → ℝ) :
    |(realForm F x - realMetric D x) - (realForm G x - realMetric E x)| ≤
      ε * realMetric W x := by
  have hf : realForm F x - realForm G x = realForm (fun i j => F i j - G i j) x := by
    simp only [realForm, sub_mul, sum_sub_distrib]
  have hd : realMetric D x - realMetric E x = ∑ i, (D i - E i) * (x i)^2 := by
    simp only [realMetric, sub_mul, sum_sub_distrib]
  rw [show (realForm F x - realMetric D x) - (realForm G x - realMetric E x) =
    (realForm F x - realForm G x) - (realMetric D x - realMetric E x) by ring, hf, hd]
  calc
    _ ≤ |realForm (fun i j => F i j - G i j) x| + |∑ i, (D i - E i) * (x i)^2| := abs_sub _ _
    _ ≤ (∑ i, (∑ j, |F i j - G i j|) * (x i)^2) + ∑ i, |D i - E i| * (x i)^2 := by
      apply add_le_add (realForm_abs_le_row _ hs x)
      refine (abs_sum_le_sum_abs (fun i => (D i - E i) * (x i)^2) univ).trans ?_
      exact sum_le_sum fun i _ => by rw [abs_mul, abs_of_nonneg (sq_nonneg (x i))]
    _ ≤ _ := by
      unfold realMetric
      rw [← sum_add_distrib, mul_sum]
      exact sum_le_sum fun i _ => by
        rw [← add_mul, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (hrow i) (sq_nonneg _)

theorem crossing_of_threshold_budget
    (F G : ℝ → ι → ι → ℝ) (D E W : ℝ → ι → ℝ) {cold hot : ℝ} (hord : cold ≤ hot)
    (hF : ∀ i j, Continuous fun t => F t i j) (hD : ∀ i, Continuous fun t => D t i)
    (hp : ∀ t i, 0 < D t i)
    (εcold εhot : ℝ)
    (hs : ∀ t i j, F t i j - G t i j = F t j i - G t j i)
    (hrow : ∀ t, t = cold ∨ t = hot → ∀ i,
      (∑ j, |F t i j - G t i j|) + |D t i - E t i| ≤
        (if t = cold then εcold else εhot) * W t i)
    (hne : cold ≠ hot)
    (hlo : ∃ x : ι → ℝ, 0 < realMetric (D cold) x ∧
      εcold * realMetric (W cold) x < realForm (G cold) x - realMetric (E cold) x)
    (hhi : ∀ x : ι → ℝ,
      realForm (G hot) x - realMetric (E hot) x + εhot * realMetric (W hot) x ≤ 0) :
    ∃ t ∈ Icc cold hot, spectrumTop (F t) (D t) = 1 := by
  obtain ⟨x, hx, hxc⟩ := hlo
  have hcl := (abs_le.mp (threshold_form_error (F cold) (G cold) (D cold) (E cold)
    (W cold) εcold (hs cold) (by simpa using hrow cold (Or.inl rfl)) x)).1
  have hl : 1 ≤ spectrumTop (F cold) (D cold) := by
    apply le_of_mul_le_mul_right _ hx
    have hh := form_le_spectrum (F cold) (D cold) (hp cold) x
    linarith only [hcl, hxc, hh]
  have hupper (y : ι → ℝ) : realForm (F hot) y ≤ realMetric (D hot) y := by
    have hh := (abs_le.mp (threshold_form_error (F hot) (G hot) (D hot) (E hot)
      (W hot) εhot (hs hot) (by simpa [hne.symm] using hrow hot (Or.inr rfl)) y)).2
    linarith only [hh, hhi y]
  have hhigh : spectrumTop (F hot) (D hot) ≤ 1 := by
    by_cases he : (values (F hot) (D hot)).Nonempty
    · exact csSup_le he (by
        rintro _ ⟨y, hy, rfl⟩
        exact (div_le_one hy).2 (hupper y))
    · rw [spectrumTop, Set.not_nonempty_iff_eq_empty.mp he, Real.sSup_empty]
      norm_num
  obtain ⟨t, ht, h⟩ := intermediate_value_Icc' hord
    (spectrum_continuous F D hF hD hp).continuousOn ⟨hhigh, hl⟩
  exact ⟨t, ht, h⟩

end Grain.Pairing.Material
