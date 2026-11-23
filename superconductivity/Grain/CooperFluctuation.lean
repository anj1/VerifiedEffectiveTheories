import Grain.CooperThermal
import Grain.EFTBounds
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Convex.Jensen

/-! The finite Gibbs variational inequalities give a two-sided bound on
the free-energy cost of the discarded square. All traces are over the
parent Fock space, including the blocked states. -/

namespace Grain.Cooper

open Matrix NormedSpace

variable {s : Type} [Fintype s] [DecidableEq s]

private theorem diagonalize {A : Matrix s s ℝ} (hA : A.IsSymm) :
    ∃ (U : Matrix s s ℝ) (a : s → ℝ),
      Uᵀ * U = 1 ∧ U * Uᵀ = 1 ∧ A = U * diagonal a * Uᵀ ∧
        exp A = U * diagonal (Real.exp ∘ a) * Uᵀ := by
  have h := Matrix.isHermitian_iff_isSymm.mpr hA
  let U := h.eigenvectorUnitary
  let a := h.eigenvalues
  have hstar : (star (U : Matrix s s ℝ)) = (U : Matrix s s ℝ)ᵀ := rfl
  have hUA : A = (U : Matrix s s ℝ) * diagonal a * (U : Matrix s s ℝ)ᵀ := by
    have he := h.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply, RCLike.ofReal_real_eq_id, Function.id_comp] at he
    change A = (U : Matrix s s ℝ) * diagonal a * star (U : Matrix s s ℝ) at he
    rwa [hstar] at he
  refine ⟨U, a, hstar ▸ Unitary.coe_star_mul_self U, hstar ▸ Unitary.coe_mul_star_self U, hUA, ?_⟩
  let V := Unitary.toUnits U
  have hV : ↑(V⁻¹) = (U : Matrix s s ℝ)ᵀ := hstar
  rw [hUA, ← hV]
  change exp ((V : Matrix s s ℝ) * diagonal a * (↑(V⁻¹) : Matrix s s ℝ)) =
    (V : Matrix s s ℝ) * diagonal (Real.exp ∘ a) * (↑(V⁻¹) : Matrix s s ℝ)
  rw [Matrix.exp_units_conj V, Matrix.exp_diagonal, Pi.exp_def]
  simp only [Real.exp_eq_exp_ℝ, Function.comp_def]

private theorem exp_conjugate (U A : Matrix s s ℝ)
    (hU : Uᵀ * U = 1) (hU' : U * Uᵀ = 1) :
    exp (Uᵀ * A * U) = Uᵀ * exp A * U := by
  let V : (Matrix s s ℝ)ˣ := ⟨U, Uᵀ, hU', hU⟩
  exact Matrix.exp_units_conj' V A

private theorem diagonal_exp_le {A : Matrix s s ℝ} (hA : A.IsSymm) (i : s) :
    Real.exp (A i i) ≤ exp A i i := by
  obtain ⟨U, a, _, hU, he, hexp⟩ := diagonalize hA
  have hd (d : s → ℝ) : (U * diagonal d * Uᵀ) i i = ∑ j, (U i j)^2 * d j := by
    rw [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [Matrix.mul_diagonal, Matrix.transpose_apply]
    ring
  have hw : ∑ j, (U i j)^2 = 1 := by
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, pow_two, Matrix.one_apply_eq]
      using congrArg (fun M : Matrix s s ℝ => M i i) hU
  rw [congrArg (fun M : Matrix s s ℝ => M i i) he, hd, hexp, hd]
  exact convexOn_exp.map_sum_le (fun j _ => sq_nonneg (U i j)) hw (fun _ _ => Set.mem_univ _)

/-- Gibbs variational inequality for the finite trace. This follows by
applying scalar Jensen in the eigenbasis of the comparison Hamiltonian,
and again with Boltzmann weights in that basis. -/
theorem log_partition_ge [Nonempty s] {A D : Matrix s s ℝ} (hA : A.IsSymm) (hD : D.IsSymm) :
    (D * exp A).trace / (exp A).trace ≤
      Real.log (exp (A + D)).trace - Real.log (exp A).trace := by
  obtain ⟨U, a, hU, hU', hAd, hE⟩ := diagonalize hA
  let D' := Uᵀ * D * U
  have hdiag : Uᵀ * A * U = diagonal a := by
    rw [hAd, ← mul_assoc Uᵀ, ← mul_assoc Uᵀ, hU, one_mul, mul_assoc, hU, mul_one]
  have hconj : Uᵀ * (A+D) * U = diagonal a + D' := by rw [mul_add, add_mul, hdiag]
  have hsym : (diagonal a + D').IsSymm := by
    unfold D' Matrix.IsSymm
    simp [hD.eq, mul_assoc]
  let z := ∑ i, Real.exp (a i)
  have hz : 0 < z := Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  have htraceA : (exp A).trace = z := by
    rw [hE, Matrix.trace_mul_comm, ← mul_assoc, hU, one_mul]
    simp [z, Function.comp_def]
  have htraceD : (D * exp A).trace = ∑ i, Real.exp (a i) * D' i i := by
    rw [hE, ← mul_assoc, ← mul_assoc, Matrix.trace_mul_comm, ← mul_assoc, ← mul_assoc Uᵀ]
    simp [Matrix.trace, D', Matrix.mul_diagonal, Function.comp_def, mul_comm]
  have htraceB : (exp (diagonal a + D')).trace = (exp (A+D)).trace := by
    rw [← hconj, exp_conjugate _ _ hU hU', Matrix.trace_mul_comm, ← mul_assoc, hU', one_mul]
  have hsum : ∑ i, Real.exp (a i + D' i i) ≤ (exp (A+D)).trace := by
    rw [← htraceB, Matrix.trace]
    exact Finset.sum_le_sum fun i _ => by
      change Real.exp (a i + D' i i) ≤ exp (diagonal a + D') i i
      simpa only [Matrix.add_apply, Matrix.diagonal_apply_eq] using diagonal_exp_le hsym i
  let w (i : s) := Real.exp (a i) / z
  have hw : ∑ i, w i = 1 := by rw [show ∑ i, w i = z/z from (Finset.sum_div ..).symm, div_self hz.ne']
  have hj := convexOn_exp.map_sum_le (w := w) (p := fun i => D' i i)
    (fun i _ => div_nonneg (Real.exp_nonneg _) hz.le) hw (fun _ _ => Set.mem_univ _)
  simp only [smul_eq_mul] at hj
  have hmean : ∑ i, w i * D' i i = (D * exp A).trace / z := by
    rw [htraceD, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [w]
    ring
  have hexp : ∑ i, w i * Real.exp (D' i i) = (∑ i, Real.exp (a i + D' i i)) / z := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [Real.exp_add]
    dsimp [w]
    ring
  rw [hmean, hexp] at hj
  have hb := hj.trans (div_le_div_of_nonneg_right hsum hz.le)
  have hpos := (Real.exp_pos _).trans_le hb
  have hbpos : 0 < (exp (A+D)).trace := (div_pos_iff_of_pos_right hz).mp hpos
  have hl := Real.log_le_log (Real.exp_pos _) hb
  rwa [Real.log_exp, Real.log_div hbpos.ne' hz.ne', ← htraceA] at hl

private theorem free_energy_difference_ge [Nonempty s] {H W : Matrix s s ℝ}
    (hH : H.IsSymm) (hW : W.IsSymm) {t : ℝ} (ht : 0 < t) :
    -gibbsMean H W t ≤ freeEnergy H t - freeEnergy (H+W) t := by
  have hs (X : Matrix s s ℝ) (hX : X.IsSymm) : ((-t⁻¹) • X).IsSymm := by
    unfold Matrix.IsSymm
    rw [Matrix.transpose_smul, hX.eq]
  have hr := log_partition_ge (hs H hH) (hs W hW)
  rw [← smul_add, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, mul_div_assoc] at hr
  change -t⁻¹ * gibbsMean H W t ≤
    Real.log (gibbsWeight (H+W) t).trace - Real.log (gibbsWeight H t).trace at hr
  have he := mul_le_mul_of_nonneg_left hr ht.le
  rw [← mul_assoc, mul_neg, mul_inv_cancel₀ ht.ne', neg_one_mul] at he
  unfold freeEnergy
  linarith

/-- For each fixed trial field and applied source, the cost of dropping
the square is bounded by its Gibbs expectations at the two endpoints.
This controls the discarded interaction without assuming factorization. -/
theorem fluctuation_cost [Nonempty s] {K : Matrix s s ℝ} (hK : K.IsSymm)
    (B : Matrix s s ℝ) {g t : ℝ} (hg : g ≠ 0) (ht : 0 < t) (eta x : ℝ) :
    let H := hamiltonian K B g eta
    let M := quadraticHamiltonian K B g eta x
    let Q := centeredPair B g eta x
    g * gibbsMean M (Qᵀ * Q) t ≤ freeEnergy M t - freeEnergy H t ∧
      freeEnergy M t - freeEnergy H t ≤ g * gibbsMean H (Qᵀ * Q) t := by
  intro H M Q
  have hH : H.IsSymm := hamiltonian_symmetric hK B g eta
  have hQ : (Qᵀ * Q).IsSymm := by simp [Matrix.IsSymm]
  have hW (c : ℝ) : (c • (Qᵀ * Q)).IsSymm := by
    simp [Matrix.IsSymm, hQ.eq]
  have eq : H = M - g • (Qᵀ * Q) := restore_square K B hg eta x
  have eq' : H + g • (Qᵀ * Q) = M := by rw [eq, sub_add_cancel]
  have hM : M.IsSymm := by
    rw [← eq']
    exact hH.add (hW g)
  have hlo := free_energy_difference_ge hM (hW (-g)) ht
  have hhi := free_energy_difference_ge hH (hW g) ht
  have hscale (A : Matrix s s ℝ) (c : ℝ) :
      gibbsMean A (c • (Qᵀ * Q)) t = c * gibbsMean A (Qᵀ * Q) t := by
    simp only [gibbsMean, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, mul_div_assoc]
  rw [hscale, neg_mul, neg_neg, neg_smul, ← sub_eq_add_neg, ← eq] at hlo
  rw [hscale, eq'] at hhi
  exact ⟨hlo, by linarith⟩

/-- A form bound on the discarded square supplies the upper endpoint
without solving the parent thermal trace. -/
theorem fluctuation_cost_of_form [Nonempty s] {K : Matrix s s ℝ} (hK : K.IsSymm)
    (B : Matrix s s ℝ) {g t : ℝ} (hg : 0 < g) (ht : 0 < t) (eta x c : ℝ)
    (hc : ∀ v : s → ℝ, ∑ i, (centeredPair B g eta x *ᵥ v) i ^ 2 ≤ c * ∑ i, (v i)^2) :
    let H := hamiltonian K B g eta
    let M := quadraticHamiltonian K B g eta x
    let Q := centeredPair B g eta x
    g * gibbsMean M (Qᵀ * Q) t ≤ freeEnergy M t - freeEnergy H t ∧
      freeEnergy M t - freeEnergy H t ≤ g * c := by
  have hb := fluctuation_cost hK B hg.ne' ht eta x
  have hu := gibbs_square_le (hamiltonian_symmetric hK B g eta) t c hc
  exact ⟨hb.1, hb.2.trans (mul_le_mul_of_nonneg_left hu hg.le)⟩

/-- Given form bounds at both sources, the finite-source response error
is enclosed using only those bounds and quadratic Gibbs expectations.
Use the minimizing total field at each source for the optimized response. -/
theorem fluctuation_response_of_forms [Nonempty s] {K : Matrix s s ℝ} (hK : K.IsSymm)
    (B : Matrix s s ℝ) {g t h : ℝ} (hg : 0 < g) (ht : 0 < t) (hh : 0 < h)
    (x₀ xₕ c₀ cₕ : ℝ)
    (bound₀ : ∀ v : s → ℝ, ∑ i, (centeredPair B g 0 x₀ *ᵥ v) i ^ 2 ≤ c₀ * ∑ i, (v i)^2)
    (boundₕ : ∀ v : s → ℝ, ∑ i, (centeredPair B g h xₕ *ᵥ v) i ^ 2 ≤ cₕ * ∑ i, (v i)^2) :
    let m (eta x : ℝ) := freeEnergy (quadraticHamiltonian K B g eta x) t
    let f (eta : ℝ) := freeEnergy (hamiltonian K B g eta) t
    let lower (eta x : ℝ) :=
      let Q := centeredPair B g eta x
      g * gibbsMean (quadraticHamiltonian K B g eta x) (Qᵀ * Q) t
    let error := (m 0 x₀ - m h xₕ) / (2*h^2) - (f 0 - f h) / (2*h^2)
    (lower 0 x₀ - g*cₕ) / (2*h^2) ≤ error ∧ error ≤ (g*c₀ - lower h xₕ) / (2*h^2) :=
  EFT.channel_response_enclosure hh
    (fluctuation_cost_of_form hK B hg ht 0 x₀ c₀ bound₀)
    (fluctuation_cost_of_form hK B hg ht h xₕ cₕ boundₕ)

end Grain.Cooper
