import Grain.ThermalTrace
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-! The finite Cooper Hamiltonian retains the pair square. A number gauge
involution commutes with the kinetic term and changes the sign of the pair
annihilator. The finite Gibbs state respects this symmetry at zero source. -/

namespace Grain.Cooper

open Matrix NormedSpace
open scoped Matrix.Norms.Operator

variable {s : Type} [Fintype s] [DecidableEq s]

def hamiltonian (K B : Matrix s s ℝ) (g eta : ℝ) : Matrix s s ℝ :=
  K - g • (Bᵀ * B) - eta • (B + Bᵀ)

noncomputable def centeredPair (B : Matrix s s ℝ) (g eta x : ℝ) : Matrix s s ℝ :=
  B - ((x - eta) / g) • 1

noncomputable def quadraticHamiltonian (K B : Matrix s s ℝ) (g eta x : ℝ) : Matrix s s ℝ :=
  K - x • (B + Bᵀ) + ((x - eta)^2 / g) • 1

/-- Keeping the centered square recovers the exact Hamiltonian for every
choice of trial field. The same decomposition holds at an applied source. -/
theorem restore_square (K B : Matrix s s ℝ) {g : ℝ} (hg : g ≠ 0) (eta x : ℝ) :
    let Q := centeredPair B g eta x
    hamiltonian K B g eta = quadraticHamiltonian K B g eta x - g • (Qᵀ * Q) := by
  intro Q
  let a := (x - eta) / g
  have hQ : Qᵀ * Q = Bᵀ * B - a • (B + Bᵀ) + (a*a) • (1 : Matrix s s ℝ) := by
    change (B - a • (1 : Matrix s s ℝ))ᵀ * (B - a • 1) = _
    simp only [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, smul_sub, smul_smul, smul_add]
    abel
  have hga : g * a = x - eta := by dsimp [a]; field_simp
  have hs : g * (a*a) = (x - eta)^2 / g := by
    rw [← mul_assoc, hga]
    dsimp [a]
    ring
  rw [hQ, smul_add, smul_sub, smul_smul g a, hga, smul_smul g (a*a), hs]
  unfold hamiltonian quadraticHamiltonian
  rw [sub_smul]
  abel

noncomputable def gibbsWeight (H : Matrix s s ℝ) (t : ℝ) : Matrix s s ℝ :=
  exp ((-t⁻¹) • H)

noncomputable def gibbsMean (H A : Matrix s s ℝ) (t : ℝ) : ℝ :=
  (A * gibbsWeight H t).trace / (gibbsWeight H t).trace

noncomputable def freeEnergy (H : Matrix s s ℝ) (t : ℝ) : ℝ :=
  -t * Real.log (gibbsWeight H t).trace

omit [DecidableEq s] in
private theorem trace_transpose_mul_self (X : Matrix s s ℝ) :
    (Xᵀ * X).trace = ∑ i, ∑ j, (X j i)^2 := by
  simp [Matrix.trace, Matrix.mul_apply, pow_two]

omit [DecidableEq s] in
private theorem trace_transpose_mul_self_pos {X : Matrix s s ℝ} (hX : X ≠ 0) :
    0 < (Xᵀ * X).trace := by
  rw [trace_transpose_mul_self]
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hX
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hj
  exact Finset.sum_pos' (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
    ⟨i, Finset.mem_univ _, Finset.sum_pos' (fun _ _ => sq_nonneg _)
      ⟨j, Finset.mem_univ _, sq_pos_of_ne_zero hi⟩⟩

private theorem gibbs_factor {H : Matrix s s ℝ} (hH : H.IsSymm) (t : ℝ) :
    ∃ V : (Matrix s s ℝ)ˣ, (V : Matrix s s ℝ)ᵀ = V ∧
      gibbsWeight H t = (V : Matrix s s ℝ) * V := by
  let A : Matrix s s ℝ := (-t⁻¹ / 2) • H
  have hA : A.IsSymm := by
    unfold A Matrix.IsSymm
    rw [Matrix.transpose_smul, hH.eq]
  obtain ⟨V, hV⟩ := Matrix.isUnit_exp A
  refine ⟨V, ?_, ?_⟩
  · rw [hV, ← Matrix.exp_transpose, hA.eq]
  · rw [hV, ← Matrix.exp_add_of_commute _ _ (Commute.refl _)]
    unfold gibbsWeight
    congr 1
    rw [← add_smul]
    congr 1
    ring

theorem partition_pos [Nonempty s] {H : Matrix s s ℝ} (hH : H.IsSymm) (t : ℝ) :
    0 < (gibbsWeight H t).trace := by
  obtain ⟨V, hV, hW⟩ := gibbs_factor hH t
  have hn : (V : Matrix s s ℝ) ≠ 0 := V.ne_zero
  simpa only [hW, hV] using trace_transpose_mul_self_pos hn

omit [DecidableEq s] in
private theorem square_trace_eq (Q V W : Matrix s s ℝ)
    (hV : Vᵀ = V) (hW : W = V * V) :
    (Qᵀ * Q * W).trace = ((Q*V)ᵀ * (Q*V)).trace := by
  rw [Matrix.transpose_mul, hV, mul_assoc V, Matrix.trace_mul_comm V,
    ← mul_assoc Qᵀ, mul_assoc (Qᵀ * Q), ← hW]

/-- The Gibbs weight is faithful. Every nonzero square has a strictly
positive expectation at finite temperature, including a centered pair square. -/
theorem gibbs_square_pos [Nonempty s] {H Q : Matrix s s ℝ} (hH : H.IsSymm)
    (hQ : Q ≠ 0) (t : ℝ) : 0 < gibbsMean H (Qᵀ * Q) t := by
  obtain ⟨V, hV, hW⟩ := gibbs_factor hH t
  have hn : Q * (V : Matrix s s ℝ) ≠ 0 := by
    intro hz
    apply hQ
    have he := congrArg (fun A : Matrix s s ℝ => A * (↑(V⁻¹) : Matrix s s ℝ)) hz
    simpa [mul_assoc] using he
  unfold gibbsMean
  apply div_pos _ (partition_pos hH t)
  rw [square_trace_eq Q _ _ hV hW]
  exact trace_transpose_mul_self_pos hn

/-- A certified quadratic-form bound on the pair square bounds its
expectation in every finite Gibbs state, independently of the spectrum. -/
theorem gibbs_square_le [Nonempty s] {H Q : Matrix s s ℝ} (hH : H.IsSymm)
    (t c : ℝ) (hc : ∀ x : s → ℝ, ∑ i, (Q *ᵥ x) i ^ 2 ≤ c * ∑ i, (x i)^2) :
    gibbsMean H (Qᵀ * Q) t ≤ c := by
  obtain ⟨V, hV, hW⟩ := gibbs_factor hH t
  unfold gibbsMean
  apply (div_le_iff₀ (partition_pos hH t)).2
  have he : gibbsWeight H t = (V : Matrix s s ℝ)ᵀ * V := by rw [hV, hW]
  rw [square_trace_eq Q _ _ hV hW, he,
    trace_transpose_mul_self, trace_transpose_mul_self, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => hc (fun j => (V : Matrix s s ℝ) j i)

omit [DecidableEq s] in
theorem hamiltonian_symmetric {K : Matrix s s ℝ} (hK : K.IsSymm)
    (B : Matrix s s ℝ) (g eta : ℝ) : (hamiltonian K B g eta).IsSymm := by
  unfold hamiltonian Matrix.IsSymm
  simp [hK.eq, add_comm (eta • Bᵀ) (eta • B)]

private def traceMap : Matrix s s ℝ →L[ℝ] ℝ :=
  ⟨traceLinearMap s ℝ ℝ, continuous_finsetSum _ fun i _ => continuous_apply_apply i i⟩

/-- The Taylor-series certificate computes the trace of the same matrix
exponential that defines the exact Gibbs state. -/
theorem checked_partition_eq (A : Matrix s s ℝ) :
    ThermalTrace.partition A = (exp A).trace := by
  have hs := exp_series_hasSum_exp' (𝕂 := ℝ) A
  have h := (hs.map traceMap traceMap.continuous).tsum_eq
  change (∑' k : ℕ, ((↑k.factorial : ℝ)⁻¹ • A ^ k).trace) = (exp A).trace at h
  simpa only [ThermalTrace.partition, Matrix.trace_smul, smul_eq_mul, div_eq_mul_inv, mul_comm] using h

/-- At any fixed source the exact finite Cooper free energy is analytic
throughout the positive-temperature axis. -/
theorem free_energy_analytic [Nonempty s] {H : Matrix s s ℝ} (hH : H.IsSymm)
    {t : ℝ} (ht : 0 < t) : AnalyticAt ℝ (freeEnergy H) t := by
  have hscale : AnalyticAt ℝ (fun u : ℝ => (-u⁻¹) • H) t :=
    ((analyticAt_id.inv ht.ne').neg.smul analyticAt_const)
  have hexp : AnalyticAt ℝ (gibbsWeight H) t :=
    AnalyticAt.comp (f := fun u : ℝ => (-u⁻¹) • H) (exp_analytic (𝕂 := ℝ) _) hscale
  have htrace : AnalyticAt ℝ (fun u => (gibbsWeight H u).trace) t :=
    AnalyticAt.comp (f := gibbsWeight H) (g := traceMap) ((traceMap (s := s)).analyticAt (gibbsWeight H t)) hexp
  exact analyticAt_id.neg.mul (htrace.log (partition_pos hH t))

/-- An involution commuting with the zero-source Hamiltonian and reversing
the pair operator forces the exact anomalous amplitude to vanish. -/
theorem gibbs_mean_zero_of_gauge (U H B : Matrix s s ℝ) (hu : U * U = 1)
    (hH : Commute U H) (hB : U * B = -(B * U)) (t : ℝ) : gibbsMean H B t = 0 := by
  have hw : Commute U (gibbsWeight H t) := (hH.smul_right (-t⁻¹)).exp_right
  have hprod : U * (B * gibbsWeight H t) = -(B * gibbsWeight H t) * U := by
    rw [← mul_assoc, hB, neg_mul, neg_mul, mul_assoc, hw.eq, ← mul_assoc]
  have hc := congrArg (fun A : Matrix s s ℝ => (A * U).trace) hprod
  change ((U * (B * gibbsWeight H t)) * U).trace =
    ((-(B * gibbsWeight H t) * U) * U).trace at hc
  rw [Matrix.trace_mul_comm _ U, ← mul_assoc U U, hu, one_mul,
    mul_assoc (-(B * gibbsWeight H t)) U U, hu, mul_one, Matrix.trace_neg] at hc
  unfold gibbsMean
  rw [show (B * gibbsWeight H t).trace = 0 by linarith, zero_div]

/-- The exact zero-source Cooper Gibbs state has zero pair amplitude and
a strictly positive pair-square expectation when the annihilator is nonzero. -/
theorem zero_source_pairing [Nonempty s] {K B U : Matrix s s ℝ} (hK : K.IsSymm)
    (hU : U.IsSymm) (hu : U * U = 1) (hUK : Commute U K)
    (hUB : U * B = -(B * U)) (hB : B ≠ 0) (g t : ℝ) :
    let H := hamiltonian K B g 0
    gibbsMean H B t = 0 ∧ 0 < gibbsMean H (Bᵀ * B) t := by
  intro H
  have hUBt : U * Bᵀ = -(Bᵀ * U) := by
    have he := congrArg Matrix.transpose hUB
    simp only [Matrix.transpose_mul, Matrix.transpose_neg, hU.eq] at he
    calc
      U * Bᵀ = -(-(U * Bᵀ)) := (neg_neg _).symm
      _ = -(Bᵀ * U) := by rw [he]
  have hc : Commute U (Bᵀ * B) := by
    change U * (Bᵀ * B) = (Bᵀ * B) * U
    rw [← mul_assoc, hUBt, neg_mul, mul_assoc, hUB, mul_neg, neg_neg, mul_assoc]
  refine ⟨gibbs_mean_zero_of_gauge U H B hu ?_ hUB t,
    gibbs_square_pos (hamiltonian_symmetric hK B g 0) hB t⟩
  simpa [H, hamiltonian] using hUK.sub_right (hc.smul_right g)

end Grain.Cooper
