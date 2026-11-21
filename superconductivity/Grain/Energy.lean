import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-! Rational matrix certificates for real variational energies. -/

namespace Grain

open scoped BigOperators

def action {ι : Type} [Fintype ι] (A : ι → ι → ℚ) (w : ι → ℚ) (i : ι) : ℚ :=
  ∑ j, A i j * w j

noncomputable def form {ι : Type} [Fintype ι] (A : ι → ι → ℚ) (x : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, (A i j : ℝ) * (x i * x j)

noncomputable def normSq {ι : Type} [Fintype ι] (x : ι → ℝ) : ℝ := ∑ i, x i ^ 2

/-- The possible normalized Rayleigh energies of a real Hamiltonian. -/
noncomputable def energies {ι : Type} [Fintype ι] (A : ι → ι → ℚ) : Set ℝ :=
  { e | ∃ x : ι → ℝ, 0 < normSq x ∧ form A x / normSq x = e }

noncomputable def ground {ι : Type} [Fintype ι] (A : ι → ι → ℚ) : ℝ :=
  sInf (energies A)

theorem weighted_lower {ι : Type} [Fintype ι]
    (A : ι → ι → ℚ) (w : ι → ℚ) (l : ℚ)
    (hsym : ∀ i j, A i j = A j i)
    (hsign : ∀ i j, i ≠ j → A i j ≤ 0)
    (hw : ∀ i, 0 < w i)
    (hrow : ∀ i, l * w i ≤ action A w i)
    (x : ι → ℝ) : (l : ℝ) * normSq x ≤ form A x := by
  have term (i j : ι) :
      ((A i j : ℚ) : ℝ) * (((w j : ℝ) / (w i : ℝ)) * x i ^ 2) +
      ((A j i : ℚ) : ℝ) * (((w i : ℝ) / (w j : ℝ)) * x j ^ 2) ≤
      2 * (((A i j : ℚ) : ℝ) * (x i * x j)) := by
    by_cases hij : i = j
    · subst j
      rw [div_self (by exact_mod_cast (hw i).ne')]
      ring_nf
      exact le_rfl
    · have hi : (0 : ℝ) < w i := by exact_mod_cast hw i
      have hj : (0 : ℝ) < w j := by exact_mod_cast hw j
      have hc : ((A i j : ℚ) : ℝ) ≤ 0 := by exact_mod_cast hsign i j hij
      have hsq := sq_nonneg ((w j : ℝ) * x i - (w i : ℝ) * x j)
      have hp : 0 < (w i : ℝ) * (w j : ℝ) := mul_pos hi hj
      have h :
          2 * (x i * x j) ≤ (w j : ℝ) / w i * x i ^ 2 + (w i : ℝ) / w j * x j ^ 2 := by
        apply (mul_le_mul_iff_left₀ hp).mp
        field_simp
        nlinarith only [hsq]
      rw [hsym j i]
      nlinarith only [mul_le_mul_of_nonpos_left h hc]
  have hterm := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
    Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) => term i j))
  have rows : (l : ℝ) * normSq x ≤
      ∑ i, ∑ j, (A i j : ℝ) * ((w j : ℝ) / (w i : ℝ) * x i ^ 2) := by
    unfold normSq
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hp : (0 : ℝ) < w i := by exact_mod_cast hw i
    have h : (l : ℝ) * (w i : ℝ) ≤ ∑ j, (A i j : ℝ) * (w j : ℝ) := by
      exact_mod_cast hrow i
    have h' := (le_div_iff₀ hp).2 h
    have hx := mul_le_mul_of_nonneg_right h' (sq_nonneg (x i))
    rw [Finset.sum_div, Finset.sum_mul] at hx
    convert hx using 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hterm
  rw [Finset.sum_comm (f := fun i j =>
    (A j i : ℝ) * ((w i : ℝ) / (w j : ℝ) * x j ^ 2))] at hterm
  unfold form
  linarith

def rayleighNumerator {ι : Type} [Fintype ι] (A : ι → ι → ℚ) (w : ι → ℚ) : ℚ :=
  ∑ i, w i * action A w i

def rationalNormSq {ι : Type} [Fintype ι] (w : ι → ℚ) : ℚ := ∑ i, w i ^ 2

theorem form_cast {ι : Type} [Fintype ι] (A : ι → ι → ℚ) (w : ι → ℚ) :
    form A (fun i => (w i : ℝ)) = (rayleighNumerator A w : ℝ) := by
  simp only [form, rayleighNumerator, action, Rat.cast_sum, Rat.cast_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem normSq_cast {ι : Type} [Fintype ι] (w : ι → ℚ) :
    normSq (fun i => (w i : ℝ)) = (rationalNormSq w : ℝ) := by
  simp [normSq, rationalNormSq]

theorem normalized_trial {ι : Type} [Fintype ι] (A : ι → ι → ℚ) (w : ι → ℚ)
    (hw : 0 < rationalNormSq w) (u : ℚ)
    (hu : rayleighNumerator A w ≤ u * rationalNormSq w) :
    ∃ e ∈ energies A, e ≤ (u : ℝ) := by
  let x : ι → ℝ := fun i => (w i : ℝ)
  have hn : 0 < normSq x := by
    rw [normSq_cast]
    exact_mod_cast hw
  refine ⟨form A x / normSq x, ⟨x, hn, rfl⟩, (div_le_iff₀ hn).2 ?_⟩
  rw [form_cast, normSq_cast]
  exact_mod_cast hu

theorem ground_bounds {ι : Type} [Fintype ι] (A : ι → ι → ℚ) (l u : ℚ)
    (hl : ∀ x, (l : ℝ) * normSq x ≤ form A x)
    (hu : ∃ e ∈ energies A, e ≤ (u : ℝ)) :
    (l : ℝ) ≤ ground A ∧ ground A ≤ (u : ℝ) := by
  have lb : ∀ e ∈ energies A, (l : ℝ) ≤ e := by
    rintro e ⟨x, hx, rfl⟩
    exact (le_div_iff₀ hx).2 (hl x)
  obtain ⟨e, he, heu⟩ := hu
  exact ⟨le_csInf ⟨e, he⟩ lb, (csInf_le ⟨(l : ℝ), lb⟩ he).trans heu⟩

theorem form_sub {ι : Type} [Fintype ι] (A B : ι → ι → ℚ) (x : ι → ℝ) :
    form (fun i j => A i j - B i j) x = form A x - form B x := by
  simp [form, sub_mul, Finset.sum_sub_distrib]

end Grain
