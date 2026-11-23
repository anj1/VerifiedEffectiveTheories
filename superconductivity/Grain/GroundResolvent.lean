import Grain.ResolventRemainder
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Matrix.Hermitian

/-! The ground-energy remainder for a rational occupation matrix with an isolated reference. -/

namespace Grain.ResolventRemainder

open scoped BigOperators Matrix

private theorem ground_eigenvector {ι : Type} [Fintype ι] [Nonempty ι]
    (A : ι → ι → ℚ) (hsym : ∀ i j, A i j = A j i) :
    ∃ x : ι → ℝ, x ≠ 0 ∧ ∀ i, ∑ j, (A i j : ℝ) * x j = ground A * x i := by
  classical
  let M : Matrix ι ι ℝ := fun i j => A i j
  let L := Matrix.toEuclideanLin M
  have hL : L.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr (by
    ext i j
    change star (A j i : ℝ) = (A i j : ℝ)
    simp only [star_trivial, hsym j i])
  have hform (x : EuclideanSpace ℝ ι) :
      inner ℝ (L x) x = form A (WithLp.ofLp x) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [star_trivial]
    change (∑ i, x.ofLp i * ∑ j, M i j * x.ofLp j) = _
    simp only [form, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by dsimp [M]; ring
  have he : energies A = Set.range (fun x : {x : EuclideanSpace ℝ ι // x ≠ 0} =>
      RCLike.re (inner ℝ (L x) x) / ‖(x : EuclideanSpace ℝ ι)‖ ^ 2) := by
    ext e
    constructor
    · rintro ⟨x, hx, rfl⟩
      let y : EuclideanSpace ℝ ι := WithLp.toLp 2 x
      have hy : ‖y‖ ^ 2 = normSq x := EuclideanSpace.real_norm_sq_eq y
      have hne : y ≠ 0 := by intro h; simp [h] at hy; linarith
      exact ⟨⟨y, hne⟩, by change RCLike.re (inner ℝ (L y) y) / ‖y‖ ^ 2 = _; rw [hform, hy]; rfl⟩
    · rintro ⟨⟨x, hx⟩, rfl⟩
      refine ⟨x.ofLp, ?_, ?_⟩
      · change 0 < ∑ i, x.ofLp i ^ 2
        rw [← EuclideanSpace.real_norm_sq_eq x]
        exact sq_pos_of_pos (norm_pos_iff.mpr hx)
      · change _ = RCLike.re (inner ℝ (L x) x) / ‖x‖ ^ 2
        rw [hform, EuclideanSpace.real_norm_sq_eq, normSq]
        rfl
  have hE : Module.End.HasEigenvalue L (ground A) := by
    simpa [ground, he, iInf] using hL.hasEigenvalue_iInf_of_finiteDimensional
  obtain ⟨x, hx⟩ := hE.exists_hasEigenvector
  obtain ⟨hxL, hne⟩ := Module.End.hasEigenvector_iff.mp hx
  refine ⟨x.ofLp, fun h => hne (WithLp.ofLp_injective 2 h), fun i => ?_⟩
  have hh := congrArg (fun y : EuclideanSpace ℝ ι => y.ofLp i)
    (Module.End.mem_eigenspace_iff.mp hxL)
  exact hh

/-- The head, tail, and other invariant blocks can be checked directly on the
matrix. A strict row bound excludes the other blocks at the ground energy. -/
theorem ground_remainder {ι τ : Type} [Fintype ι] [Fintype τ] [DecidableEq τ]
    (A : ι → ι → ℚ) (idx : Option τ → ι) (D v : τ → ℚ) (T : τ → τ → ℚ)
    {gap g B V : ℚ}
    (hsym : ∀ i j, A i j = A j i) (hsign : ∀ i j, i ≠ j → A i j ≤ 0)
    (hinj : Function.Injective idx)
    (hcross : ∀ i j, j ∉ Set.range idx → A (idx i) j = 0)
    (hother : ∀ i, i ∉ Set.range idx → A (idx none) (idx none) < Grain.action A 1 i)
    (hhead : ∀ i, A (idx none) (idx (some i)) = -g * v i)
    (htail : ∀ i j, A (idx (some i)) (idx (some j)) =
      (if i = j then A (idx none) (idx none) + D i else 0) - g * T i j)
    (hg : 0 < g) (hgap : 0 < gap) (hsmall : g * B < gap)
    (hB0 : 0 ≤ B) (hV0 : 0 ≤ V) (hD : ∀ i, gap ≤ D i)
    (hB : ∀ i, ∑ j, |T i j| ≤ B) (hv : ∀ i, |v i| ≤ 1) (hV : ∑ j, |v j| ≤ V) :
    let u := fun i => v i / D i
    let w := fun i => Grain.action T u i / D i
    let polynomial := A (idx none) (idx none) - g ^ 2 * (∑ i, v i * u i) -
      g ^ 3 * (∑ i, v i * w i)
    |ground A - (polynomial : ℝ)| ≤ budget gap g B V := by
  classical
  let e₀ := A (idx none) (idx none)
  let C : ι → ι → ℝ := fun i j => A i j
  have : Nonempty ι := ⟨idx none⟩
  obtain ⟨x, hne, hx⟩ := ground_eigenvector A hsym
  have hl (i : ι) : (Finset.univ.inf' Finset.univ_nonempty (Grain.action A 1)) * (1 : ι → ℚ) i ≤
      Grain.action A 1 i := by
    rw [Pi.one_apply, mul_one]
    exact Finset.inf'_le (Grain.action A 1) (Finset.mem_univ i)
  have hle : ground A ≤ e₀ := by
    apply (ground_bounds A _ e₀ (weighted_lower A 1 _ hsym hsign (by simp) hl) ?_).2
    let trial : ι → ℚ := fun i => if i = idx none then 1 else 0
    apply normalized_trial A trial
    · simp [rationalNormSq, trial]
    · simp [rayleighNumerator, rationalNormSq, Grain.action, trial, e₀, apply_ite]
  have sum_active (i : Option τ) :
      ∑ j, C (idx i) j * x j = ∑ j, C (idx i) (idx j) * x (idx j) := by
    calc
      _ = ∑ j ∈ Finset.univ.image idx, C (idx i) j * x j := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro j _ hj
        change (A (idx i) j : ℝ) * x j = 0
        rw [hcross i j (by simpa using hj), Rat.cast_zero, zero_mul]
      _ = _ := Finset.sum_image (fun _ _ _ _ h => hinj h)
  have active_ne : x (idx none) ≠ 0 ∨ (fun j => x (idx (some j))) ≠ 0 := by
    by_contra! hz
    obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun i => |x i|)
      (Finset.univ_nonempty (α := ι))
    have hi_pos : 0 < |x i| := by
      obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
        by_contra! h
        exact hne (funext h)
      exact (abs_pos.mpr hj).trans_le (hi j (Finset.mem_univ j))
    have hi_other : i ∉ Set.range idx := by
      rintro ⟨j, rfl⟩
      cases j with
      | none => simp [hz.1] at hi_pos
      | some j =>
        have hj := congrFun hz.2 j
        simp only [Pi.zero_apply] at hj
        simp [hj] at hi_pos
    let off := Finset.univ.erase i
    have hrow : (e₀ : ℝ) < C i i + ∑ j ∈ off, C i j := by
      have hh : (e₀ : ℝ) < ((Grain.action A 1 i : ℚ) : ℝ) := by
        exact_mod_cast hother i hi_other
      simp only [Grain.action, Pi.one_apply, mul_one, Rat.cast_sum] at hh
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)] at hh
      simpa [C, off, add_comm] using hh
    have heq : C i i * x i + ∑ j ∈ off, C i j * x j = ground A * x i := by
      have hh := hx i
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), add_comm] at hh
      exact hh
    have hdiag : 0 < C i i - ground A := by
      have hoff : ∑ j ∈ off, C i j ≤ 0 := Finset.sum_nonpos fun j hj => by
        change (A i j : ℝ) ≤ 0
        exact_mod_cast hsign i j (Finset.ne_of_mem_erase hj).symm
      linarith
    have hbound : |∑ j ∈ off, C i j * x j| ≤ -(∑ j ∈ off, C i j) * |x i| := by
      rw [← Finset.sum_neg_distrib, Finset.sum_mul]
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro j hj
      have hc : C i j ≤ 0 := by
        change (A i j : ℝ) ≤ 0
        exact_mod_cast hsign i j (Finset.ne_of_mem_erase hj).symm
      rw [abs_mul, abs_of_nonpos hc]
      exact mul_le_mul_of_nonneg_left (hi j (Finset.mem_univ j)) (neg_nonneg.mpr hc)
    rw [show (∑ j ∈ off, C i j * x j) = -(C i i - ground A) * x i by linarith,
      abs_mul, abs_neg, abs_of_pos hdiag] at hbound
    have := (mul_le_mul_iff_of_pos_right hi_pos).mp hbound
    linarith
  let shift := ground A - (e₀ : ℝ)
  let y := fun i => x (idx (some i))
  have hsub (i : Option τ) :
      C (idx i) (idx none) * x (idx none) + ∑ j : τ, C (idx i) (idx (some j)) * y j =
        ground A * x (idx i) := by
    have hh := hx (idx i)
    change (∑ j, C (idx i) j * x j) = _ at hh
    rwa [sum_active, Fintype.sum_option] at hh
  have ht (i : τ) : ((D i : ℝ) - shift) * y i =
      (g : ℝ) * (x (idx none) * (v i : ℝ) + action (fun i j => (T i j : ℝ)) y i) := by
    have hh := hsub (some i)
    have hd (j : τ) : C (idx (some i)) (idx (some j)) =
        (if i = j then (e₀ : ℝ) + (D i : ℝ) else 0) - (g : ℝ) * T i j := by
      by_cases h : i = j <;> simpa [C, h] using
        congrArg (fun q : ℚ => (q : ℝ)) (htail i j)
    have hv' : C (idx (some i)) (idx none) = -(g : ℝ) * v i := by
      simp [C, hsym (idx (some i)) (idx none), hhead]
    have hsum : (∑ j : τ, (if i = j then (e₀ : ℝ) + D i else 0) * y j) =
        ((e₀ : ℝ) + D i) * y i := by simp [ite_mul]
    simp_rw [hv', hd, sub_mul, Finset.sum_sub_distrib, hsum, mul_assoc, ← Finset.mul_sum] at hh
    dsimp [shift, action]
    linear_combination hh
  have hh : shift * x (idx none) = -(g : ℝ) * dot (fun i => (v i : ℝ)) y := by
    have hs := hsub none
    simp only [C, hhead, Rat.cast_mul, Rat.cast_neg, mul_assoc, ← Finset.mul_sum] at hs
    dsimp [shift, dot, e₀]
    linear_combination -hs
  have he := eigenvalue_remainder (fun i => (D i : ℝ)) (fun i j => (T i j : ℝ))
    (fun i => (v i : ℝ)) y (gap := (gap : ℝ)) (B := (B : ℝ)) (V := (V : ℝ))
    (by exact_mod_cast hg) (sub_nonpos.mpr hle) (by exact_mod_cast hgap)
    (by exact_mod_cast hsmall) (by exact_mod_cast hB0) (by exact_mod_cast hV0)
    (fun i => by exact_mod_cast hD i) (fun i => by exact_mod_cast hB i)
    (fun i => by exact_mod_cast hv i) (by exact_mod_cast hV) active_ne ht hh
  dsimp
  push_cast [Grain.action]
  dsimp [shift, e₀, action, dot] at he
  convert he using 2
  ring

end Grain.ResolventRemainder
