import Grain.EFTBounds

/-! Rational checks for a trial-energy shell reduction. -/

namespace Grain.EFT

open Phonon
open scoped BigOperators

variable {p q : Type} [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]

def shift {ι : Type} [DecidableEq ι] (A : ι → ι → ℚ) (z : ℚ) (i j : ι) : ℚ :=
  A i j - if i = j then z else 0

theorem form_shift {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → ℚ) (z : ℚ) (x : ι → ℝ) :
    form (shift A z) x = form A x - (z : ℝ) * normSq x := by
  rw [show shift A z = fun i j => A i j - (if i = j then z else 0) from rfl, form_sub]
  congr 1
  simp only [form, normSq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [apply_ite, ite_mul, pow_two]

def shellMatrix (A : p → p → ℚ) (B : q → p → ℚ) (D : q → q → ℚ) :
    p ⊕ q → p ⊕ q → ℚ
  | .inl i, .inl j => A i j
  | .inl i, .inr j => B j i
  | .inr i, .inl j => B i j
  | .inr i, .inr j => D i j

def residual (B : q → p → ℚ) (D : q → q → ℚ) (W : q → p → ℚ) (i : q) (j : p) : ℚ :=
  B i j + ∑ k, D i k * W k j

def lifted (A : p → p → ℚ) (B : q → p → ℚ) (D : q → q → ℚ) (W : q → p → ℚ)
    (i j : p) : ℚ :=
  A i j + ∑ k, (B k i * W k j + W k i * residual B D W k j)

private noncomputable def mulVec (M : q → p → ℚ) (x : p → ℝ) (i : q) : ℝ :=
  ∑ j, (M i j : ℝ) * x j

omit [DecidableEq p] [DecidableEq q] in
private theorem shell_form (A : p → p → ℚ) (B : q → p → ℚ) (D : q → q → ℚ)
    (x : p → ℝ) (y : q → ℝ) :
    form (shellMatrix A B D) (Sum.elim x y) =
      form A x + 2 * Phonon.inner y (mulVec B x) + form D y := by
  simp only [form, Fintype.sum_sum_type, shellMatrix, Sum.elim_inl, Sum.elim_inr,
    Finset.sum_add_distrib, Phonon.inner, mulVec, Finset.mul_sum]
  rw [Finset.sum_comm (f := fun i j => (B j i : ℝ) * (x i * y j))]
  have h : (∑ i, ∑ j, (B i j : ℝ) * (x j * y i)) =
      ∑ i, ∑ j, y i * ((B i j : ℝ) * x j) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [mul_comm (y _) (x _), h]
  simp only [← Finset.mul_sum]
  ring

omit [DecidableEq p] [DecidableEq q] in
private theorem mulVec_residual (B : q → p → ℚ) (D : q → q → ℚ) (W : q → p → ℚ)
    (x : p → ℝ) (i : q) :
    mulVec (residual B D W) x i = mulVec B x i + mulVec D (mulVec W x) i := by
  simp only [mulVec, residual, Rat.cast_add, Rat.cast_sum, Rat.cast_mul, add_mul,
    Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [DecidableEq p] [DecidableEq q] in
private theorem form_lifted (A : p → p → ℚ) (B : q → p → ℚ) (D : q → q → ℚ)
    (W : q → p → ℚ) (x : p → ℝ) :
    form (lifted A B D W) x = form (shellMatrix A B D) (Sum.elim x (mulVec W x)) := by
  rw [shell_form]
  have hcross (M N : q → p → ℚ) :
      (∑ i, ∑ j, (∑ k, (M k i : ℝ) * N k j) * (x i * x j)) =
        Phonon.inner (mulVec M x) (mulVec N x) := by
    simp only [Finset.sum_mul, Phonon.inner, mulVec]
    conv_lhs =>
      arg 2
      ext i
      rw [Finset.sum_comm]
    rw [Finset.sum_comm (f := fun i k => ∑ j, (M k i : ℝ) * N k j * (x i * x j))]
    apply Finset.sum_congr rfl
    intro k _
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [form, lifted, Rat.cast_add, Rat.cast_sum, Rat.cast_mul,
    Finset.sum_add_distrib, add_mul]
  rw [hcross, hcross]
  simp only [Phonon.inner, mulVec_residual, mul_add, Finset.sum_add_distrib]
  have hd : (∑ i, mulVec W x i * mulVec D (mulVec W x) i) =
      ∑ i, ∑ j, (D i j : ℝ) * (mulVec W x i * mulVec W x j) := by
    simp only [mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring_nf
  rw [hd]
  simp_rw [mul_comm (mulVec B x _) (mulVec W x _)]
  ring

omit [DecidableEq p] [DecidableEq q] in
private theorem shell_expand (A : p → p → ℚ) (B : q → p → ℚ) (D : q → q → ℚ)
    (W : q → p → ℚ) (hD : ∀ i j, D i j = D j i) (x : p → ℝ) (y : q → ℝ) :
    form (shellMatrix A B D) (Sum.elim x (mulVec W x + y)) =
      form (shellMatrix A B D) (Sum.elim x (mulVec W x)) +
        2 * Phonon.inner y (mulVec (residual B D W) x) + form D y := by
  simp only [shell_form]
  simp only [Pi.add_apply, Phonon.inner, mulVec_residual, form,
    add_mul, mul_add, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => (D i j : ℝ) * (mulVec W x i * y j))]
  have hcross : (∑ j, ∑ i, (D i j : ℝ) * (mulVec W x i * y j)) =
      ∑ j, ∑ i, y j * ((D j i : ℝ) * mulVec W x i) := by
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    rw [hD i j]
    ring
  rw [hcross]
  have hcross' : (∑ i, ∑ j, (D i j : ℝ) * (y i * mulVec W x j)) =
      ∑ i, ∑ j, y i * ((D i j : ℝ) * mulVec W x j) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hcross']
  simp only [← Finset.mul_sum]
  have hm (i : q) : (∑ j, (D i j : ℝ) * mulVec W x j) = mulVec D (mulVec W x) i := rfl
  simp_rw [hm]
  ring

omit [DecidableEq p] [DecidableEq q] in
private theorem norm_sum (x : p → ℝ) (y : q → ℝ) :
    normSq (Sum.elim x y) = normSq x + normSq y := by
  simp [normSq, Fintype.sum_sum_type]

/-- A row-sum test supplies the pivot bound on the discarded block. -/
theorem pivot_lower (D : q → q → ℚ) (hD : ∀ i j, D i j = D j i) (δ : ℚ)
    (h : ∀ i, δ + (∑ j, if j = i then 0 else |D i j|) ≤ D i i) (y : q → ℝ) :
    (δ : ℝ) * normSq y ≤ form D y := by
  let C (i j : q) := if i = j then D i i else -|D i j|
  have hc := weighted_lower C (fun _ => 1) δ
    (fun i j => by by_cases he : i = j <;> simp [C, he, eq_comm (a := j), hD i j])
    (fun i j he => by simp [C, he]) (fun _ => by norm_num)
    (fun i => by
      simp only [action, mul_one]
      have he (j : q) : C i j = (if i = j then D i i else 0) -
          (if j = i then 0 else |D i j|) := by
        by_cases hj : j = i <;> simp_all [C, eq_comm (a := i)]
      simp_rw [he, Finset.sum_sub_distrib]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      linarith [h i]) (fun i => |y i|)
  simp only [normSq, sq_abs] at hc
  refine hc.trans (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_)
  by_cases hij : i = j
  · subst j
    simp [C]
  · simp only [C, hij, ite_false, Rat.cast_neg, Rat.cast_abs, ← abs_mul, neg_mul]
    exact neg_abs_le _

/-- An exact retained-space LDLᵀ decomposition checks a quadratic lower bound. -/
theorem gram_lower (L : p → p → ℚ) (d : p → ℚ) (A : p → p → ℚ) (s : ℚ)
    (hd : ∀ k, 0 ≤ d k)
    (h : ∀ i j, shift A s i j = ∑ k, L i k * d k * L j k) (x : p → ℝ) :
    (s : ℝ) * normSq x ≤ form A x := by
  have he : form (shift A s) x = ∑ k, (d k : ℝ) * (∑ i, (L i k : ℝ) * x i)^2 := by
    simp only [form, h, Rat.cast_sum, Rat.cast_mul, Finset.sum_mul, pow_two]
    conv_lhs =>
      arg 2
      ext i
      rw [Finset.sum_comm]
    rw [Finset.sum_comm (f := fun i k => ∑ j, (L i k : ℝ) * d k * L j k * (x i * x j))]
    apply Finset.sum_congr rfl
    intro k _
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [form_shift] at he
  have hp : 0 ≤ ∑ k, (d k : ℝ) * (∑ i, (L i k : ℝ) * x i)^2 :=
    Finset.sum_nonneg fun k _ => mul_nonneg (by exact_mod_cast hd k) (sq_nonneg _)
  linarith

omit [DecidableEq p] in
/-- A lower endpoint at distance s below the trial energy follows from the inexact lift. -/
theorem shell_lower (A : p → p → ℚ) (B : q → p → ℚ) (D : q → q → ℚ)
    (W : q → p → ℚ) (δ ε s : ℚ) (hD : ∀ i j, D i j = D j i) (hδ : 0 < δ) (hs : 0 ≤ s)
    (hp : ∀ i, δ + (∑ j, if j = i then 0 else |D i j|) ≤ D i i)
    (hr : (∑ i, ∑ j, residual B D W i j ^ 2) ≤ δ * ε)
    (hl : ∀ x, ((ε - s : ℚ) : ℝ) * normSq x ≤ form (lifted A B D W) x)
    (x : p ⊕ q → ℝ) :
    -(s : ℝ) * normSq x ≤ form (shellMatrix A B D) x := by
  let u := x ∘ Sum.inl
  let v := x ∘ Sum.inr
  have hx : Sum.elim u v = x := by funext i; cases i <;> rfl
  have herr : ∀ a : p → ℝ, normSq (mulVec (residual B D W) a) ≤
      (δ : ℝ) * (ε : ℝ) * normSq a := by
    intro a
    refine (frobenius_residual (fun i j => (residual B D W i j : ℝ)) a).trans ?_
    apply mul_le_mul_of_nonneg_right _ (normSq_nonneg a)
    exact_mod_cast hr
  have h := (lifted_enclosure (fun (a : p → ℝ) (b : q → ℝ) =>
    form (shellMatrix A B D) (Sum.elim a b)) (mulVec W) (mulVec (residual B D W))
    (form D) (by exact_mod_cast hδ) (pivot_lower D hD δ hp)
    (shell_expand A B D W hD) herr u).1 v
  rw [← form_lifted, hx] at h
  have hl' := hl u
  push_cast at hl'
  have hsu : 0 ≤ (s : ℝ) * normSq v := mul_nonneg (by exact_mod_cast hs) (normSq_nonneg v)
  nth_rw 1 [← hx]
  rw [norm_sum]
  linarith

omit [DecidableEq p] [DecidableEq q] in
/-- A retained-space trial gives a full trial by applying the same lift. -/
theorem shell_upper (A : p → p → ℚ) (B : q → p → ℚ) (D : q → q → ℚ)
    (W : q → p → ℚ) (s : ℚ) (hs : 0 ≤ s) (u : p → ℚ)
    (hn : 0 < rationalNormSq u)
    (ht : rayleighNumerator (lifted A B D W) u ≤ s * rationalNormSq u) :
    let x := Sum.elim u (fun i => ∑ j, W i j * u j)
    0 < normSq (fun i => (x i : ℝ)) ∧
      form (shellMatrix A B D) (fun i => (x i : ℝ)) ≤ (s : ℝ) * normSq (fun i => (x i : ℝ)) := by
  let v (i : p) : ℝ := u i
  have he : (fun i => ((Sum.elim u (fun k => ∑ j, W k j * u j) i : ℚ) : ℝ)) =
      Sum.elim v (mulVec W v) := by
    funext i
    cases i <;> simp [v, mulVec]
  dsimp only
  rw [he, norm_sum, ← form_lifted]
  have hpos : 0 < normSq v := by rw [normSq_cast]; exact_mod_cast hn
  refine ⟨add_pos_of_pos_of_nonneg hpos (normSq_nonneg _), ?_⟩
  have hb : form (lifted A B D W) v ≤ (s : ℝ) * normSq v := by
    rw [form_cast, normSq_cast]
    exact_mod_cast ht
  exact hb.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (normSq_nonneg _))
    (by exact_mod_cast hs))

end Grain.EFT
