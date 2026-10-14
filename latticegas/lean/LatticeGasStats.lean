import Mathlib

/-!
A conditional finite-sample confidence theorem.  The independence and
sub-Gaussian assumptions are explicit: a deterministic PRNG run does not
establish either assumption.  Mathlib supplies the Chernoff/Hoeffding bound.
-/
namespace LatticeGas.Statistics

open MeasureTheory ProbabilityTheory
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
variable [IsProbabilityMeasure μ]

theorem oneSidedConfidence {X : ℕ → Ω → ℝ} (h_indep : iIndepFun X μ)
    {c : NNReal} {n : ℕ}
    (h_subG : ∀ i < n, HasSubgaussianMGF (X i) c μ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (h_meas : MeasurableSet {ω | ε ≤ ∑ i ∈ Finset.range n, X i ω}) :
    1 - Real.exp (-ε ^ 2 / (2 * n * c)) ≤
      μ.real {ω | ∑ i ∈ Finset.range n, X i ω < ε} := by
  have htail := ProbabilityTheory.HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun
    h_indep h_subG hε
  have hcompl : {ω | ∑ i ∈ Finset.range n, X i ω < ε} =
      {ω | ε ≤ ∑ i ∈ Finset.range n, X i ω}ᶜ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
    exact lt_iff_not_ge
  rw [hcompl, measureReal_compl h_meas, probReal_univ]
  linarith

end LatticeGas.Statistics
