import Grain.Energy
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! Exact elimination for finite matrices. The spectral shift is made before
eliminating. The same shifted matrix is used at both steps. -/

namespace Grain

open Matrix
open scoped Matrix

variable {K a b c : Type*} [Field K]
variable [Fintype a] [Fintype b] [Fintype c]
variable [DecidableEq a] [DecidableEq b] [DecidableEq c]

noncomputable def schur (M : Matrix (a ⊕ b) (a ⊕ b) K) : Matrix a a K :=
  M.toBlocks₁₁ - M.toBlocks₁₂ * M.toBlocks₂₂⁻¹ * M.toBlocks₂₁

omit [DecidableEq a] [DecidableEq b] in
private theorem mulVec_blocks (M : Matrix (a ⊕ b) (a ⊕ b) K)
    (x : a → K) (y : b → K) :
    M *ᵥ Sum.elim x y = Sum.elim
      (M.toBlocks₁₁ *ᵥ x + M.toBlocks₁₂ *ᵥ y)
      (M.toBlocks₂₁ *ᵥ x + M.toBlocks₂₂ *ᵥ y) := by
  nth_rw 1 [← Matrix.fromBlocks_toBlocks M]
  exact Matrix.fromBlocks_mulVec _ _ _ _ (Sum.elim x y)

omit [DecidableEq a] in
/-- The Schur complement computes the retained response after the eliminated
rows have been set to zero. The extension is uniquely determined. -/
theorem schur_response (M : Matrix (a ⊕ b) (a ⊕ b) K)
    (h : IsUnit M.toBlocks₂₂) (x r : a → K) :
    schur M *ᵥ x = r ↔
      ∃! y : b → K, M *ᵥ Sum.elim x y = Sum.elim r 0 := by
  let D := M.toBlocks₂₂
  let C := M.toBlocks₂₁
  let y := -(D⁻¹ *ᵥ (C *ᵥ x))
  have hy : D *ᵥ y = -(C *ᵥ x) := by
    simp only [y, Matrix.mulVec_neg, Matrix.mulVec_mulVec]
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv D ((Matrix.isUnit_iff_isUnit_det D).1 h),
      Matrix.one_mul]
  have hresponse : schur M *ᵥ x = M.toBlocks₁₁ *ᵥ x + M.toBlocks₁₂ *ᵥ y := by
    rw [schur, Matrix.sub_mulVec]
    simp only [y, D, C, Matrix.mulVec_neg, Matrix.mulVec_mulVec,
      Matrix.mul_assoc, sub_eq_add_neg]
  have htail (z : b → K) (hz : C *ᵥ x + D *ᵥ z = 0) : z = y := by
    apply Matrix.mulVec_injective_of_isUnit h
    change D *ᵥ z = D *ᵥ y
    rw [hy]
    exact eq_neg_of_add_eq_zero_left ((add_comm _ _).trans hz)
  constructor
  · intro hx
    refine ⟨y, ?_, ?_⟩
    · change M *ᵥ Sum.elim x y = Sum.elim r 0
      rw [mulVec_blocks, ← hresponse, hx]
      change Sum.elim r (C *ᵥ x + D *ᵥ y) = Sum.elim r 0
      rw [hy, add_neg_cancel]
    · intro z hz
      rw [mulVec_blocks] at hz
      apply htail
      funext j
      exact congrFun hz (Sum.inr j)
  · rintro ⟨z, hz, _⟩
    rw [mulVec_blocks] at hz
    have hzy := htail z (funext fun j => congrFun hz (Sum.inr j))
    rw [hresponse, ← hzy]
    exact funext fun i => congrFun hz (Sum.inl i)

omit [DecidableEq a] in
/-- The same response characterization with an existential extension. -/
theorem schur_response_iff (M : Matrix (a ⊕ b) (a ⊕ b) K)
    (h : IsUnit M.toBlocks₂₂) (x r : a → K) :
    schur M *ᵥ x = r ↔ ∃ y : b → K, M *ᵥ Sum.elim x y = Sum.elim r 0 := by
  refine (schur_response M h x r).trans ⟨ExistsUnique.exists, ?_⟩
  rintro ⟨y, hy⟩
  refine ⟨y, hy, fun z hz => Matrix.mulVec_injective_of_isUnit h ?_⟩
  rw [mulVec_blocks] at hy hz
  apply add_left_cancel (a := M.toBlocks₂₁ *ᵥ x)
  exact funext fun j => (congrFun hz (Sum.inr j)).trans (congrFun hy (Sum.inr j)).symm

/-- Put the two eliminated blocks next to one another without changing
any matrix entries. -/
def groupEliminated (M : Matrix ((a ⊕ b) ⊕ c) ((a ⊕ b) ⊕ c) K) :
    Matrix (a ⊕ (b ⊕ c)) (a ⊕ (b ⊕ c)) K :=
  M.submatrix (Equiv.sumAssoc a b c).symm (Equiv.sumAssoc a b c).symm

omit [DecidableEq a] [DecidableEq b] [DecidableEq c] in
private theorem grouped_response (M : Matrix ((a ⊕ b) ⊕ c) ((a ⊕ b) ⊕ c) K)
    (x r : a → K) (y : b → K) (z : c → K) :
    groupEliminated M *ᵥ Sum.elim x (Sum.elim y z) = Sum.elim r 0 ↔
      M *ᵥ Sum.elim (Sum.elim x y) z = Sum.elim (Sum.elim r 0) 0 := by
  let e := Equiv.sumAssoc a b c
  have hin : Sum.elim x (Sum.elim y z) ∘ e = Sum.elim (Sum.elim x y) z := by
    funext i
    rcases i with (i | i) | i <;> rfl
  have hout : Sum.elim r (0 : b ⊕ c → K) ∘ e = Sum.elim (Sum.elim r 0) 0 := by
    funext i
    rcases i with (i | i) | i <;> rfl
  change M.submatrix e.symm e.symm *ᵥ _ = _ ↔ _
  rw [Matrix.submatrix_mulVec_equiv, Equiv.symm_symm, hin, ← hout]
  exact ⟨fun h => funext fun i => by simpa [Function.comp] using congrFun h (e i),
    fun h => funext fun i => by simpa [Function.comp] using congrFun h (e.symm i)⟩

omit [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b] in
private theorem groupedPivot_schur (M : Matrix ((a ⊕ b) ⊕ c) ((a ⊕ b) ⊕ c) K) :
    schur (groupEliminated M).toBlocks₂₂ = (schur M).toBlocks₂₂ := by
  ext i j
  rfl

omit [Fintype a] [DecidableEq a] in
/-- The direct eliminated block is nonsingular exactly when the second
pivot is nonsingular, assuming the first pivot is nonsingular. -/
theorem grouped_pivot_isUnit_iff (M : Matrix ((a ⊕ b) ⊕ c) ((a ⊕ b) ⊕ c) K)
    (h : IsUnit M.toBlocks₂₂) :
    IsUnit (groupEliminated M).toBlocks₂₂ ↔ IsUnit (schur M).toBlocks₂₂ := by
  let P := (groupEliminated M).toBlocks₂₂
  let : Invertible P.toBlocks₂₂ :=
    (show IsUnit P.toBlocks₂₂ from h).nonempty_invertible.some
  have hblock := Matrix.isUnit_fromBlocks_iff_of_invertible₂₂
    (A := P.toBlocks₁₁) (B := P.toBlocks₁₂) (C := P.toBlocks₂₁) (D := P.toBlocks₂₂)
  rw [Matrix.fromBlocks_toBlocks] at hblock
  change IsUnit P ↔ _
  rw [← groupedPivot_schur M]
  simpa only [schur, invOf_eq_nonsing_inv] using hblock

omit [DecidableEq a] in
/-- Exact quotient identity for successive Schur complements. -/
theorem schur_compose (M : Matrix ((a ⊕ b) ⊕ c) ((a ⊕ b) ⊕ c) K)
    (h₁ : IsUnit M.toBlocks₂₂) (h₂ : IsUnit (schur M).toBlocks₂₂) :
    schur (schur M) = schur (groupEliminated M) := by
  have hd := (grouped_pivot_isUnit_iff M h₁).2 h₂
  apply Matrix.mulVec_injective
  funext x
  let r := schur (schur M) *ᵥ x
  have hr : schur (schur M) *ᵥ x = r := rfl
  obtain ⟨y, hy⟩ := (schur_response_iff _ h₂ x r).1 hr
  obtain ⟨z, hz⟩ := (schur_response_iff _ h₁ (Sum.elim x y) (Sum.elim r 0)).1 hy
  exact ((schur_response_iff _ hd x r).2 ⟨Sum.elim y z, (grouped_response M x r y z).2 hz⟩).symm

omit [DecidableEq a] in
/-- Exact elimination at a spectral parameter preserves the existence of a
nonzero solution. The lift is unique for each retained vector. -/
theorem schur_kernel_iff (M : Matrix (a ⊕ b) (a ⊕ b) K) (h : IsUnit M.toBlocks₂₂) :
    (∃ x : a → K, x ≠ 0 ∧ schur M *ᵥ x = 0) ↔
    ∃ v : a ⊕ b → K, v ≠ 0 ∧ M *ᵥ v = 0 := by
  have hz : (Sum.elim (0 : a → K) (0 : b → K)) = 0 := by ext (i | i) <;> rfl
  constructor
  · rintro ⟨x, hx, hMx⟩
    obtain ⟨y, hy⟩ := (schur_response_iff M h x 0).1 hMx
    refine ⟨Sum.elim x y, fun he => hx ?_, hy.trans hz⟩
    exact funext fun i => congrFun he (Sum.inl i)
  · rintro ⟨v, hv, hMv⟩
    let x := v ∘ Sum.inl
    let y := v ∘ Sum.inr
    have huv : Sum.elim x y = v := by ext (i | i) <;> rfl
    have hy : M *ᵥ Sum.elim x y = Sum.elim (0 : a → K) (0 : b → K) := by
      rw [huv, hMv, hz]
    refine ⟨x, ?_, (schur_response_iff M h x 0).2 ⟨y, hy⟩⟩
    intro hx
    have ⟨_, _, unique⟩ := (schur_response M h (0 : a → K) 0).1 (Matrix.mulVec_zero _)
    rw [hx] at hy
    have h0 : M *ᵥ Sum.elim (0 : a → K) (0 : b → K) =
        Sum.elim (0 : a → K) (0 : b → K) := by rw [hz, Matrix.mulVec_zero]
    exact hv (huv.symm.trans (by rw [hx, (unique y hy).trans (unique 0 h0).symm, hz]))

/-- Reindexing a matrix and its vectors preserves its nonzero kernel. -/
theorem submatrix_kernel_iff {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : Matrix ι ι K) (e : κ ≃ ι) :
    (∃ x : κ → K, x ≠ 0 ∧ M.submatrix e e *ᵥ x = 0) ↔
      ∃ v : ι → K, v ≠ 0 ∧ M *ᵥ v = 0 := by
  constructor
  · rintro ⟨x, hx, he⟩
    rw [Matrix.submatrix_mulVec_equiv] at he
    refine ⟨x ∘ e.symm, fun h => hx ?_, ?_⟩
    · funext i
      simpa [Function.comp] using congrFun h (e i)
    · funext i
      simpa [Function.comp] using congrFun he (e.symm i)
  · rintro ⟨v, hv, he⟩
    refine ⟨v ∘ e, fun h => hv ?_, ?_⟩
    · funext i
      simpa [Function.comp] using congrFun h (e.symm i)
    · rw [Matrix.submatrix_mulVec_equiv]
      have : (v ∘ e) ∘ e.symm = v := by funext i; simp [Function.comp]
      rw [this, he]
      rfl

end Grain
