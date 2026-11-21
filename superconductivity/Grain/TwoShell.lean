import Grain.Schur
import Mathlib.LinearAlgebra.Matrix.Gershgorin

/-! The seven-orbital reduced BCS model with two eliminable shells. -/

namespace Grain.TwoShell

open Matrix
open scoped Matrix

abbrev Occupation := Fin 7 → Fin 3

def electronCount (a : Occupation) : ℕ := ∑ i, (a i).val
def pairNumber (a : Occupation) : ℕ := ∑ i : Fin 7, if a i = 2 then 1 else 0
abbrev Sector (n : ℕ) := {a : Occupation // electronCount a = n}

noncomputable instance (n : ℕ) : Fintype (Sector n) := Fintype.ofFinite _

/-- The source loses a pair and the destination gains one. -/
def move (a : Occupation) (source destination : Fin 7) : Occupation :=
  fun i => if i = source then 0 else if i = destination then 2 else a i

def Hop (a b : Occupation) : Prop :=
  ∃ source destination, a source = 2 ∧ a destination = 0 ∧ b = move a source destination

instance (a b : Occupation) : Decidable (Hop a b) := by unfold Hop; infer_instance

theorem Hop.reverse {a b : Occupation} (h : Hop a b) : Hop b a := by
  obtain ⟨i, j, hi, hj, rfl⟩ := h
  have hij : i ≠ j := by
    intro he
    subst j
    have : (2 : Fin 3) = 0 := hi.symm.trans hj
    contradiction
  refine ⟨j, i, by simp [move, hij.symm], by simp [move], ?_⟩
  funext k
  by_cases hki : k = i
  · subst k
    simp [move, hij, hi]
  by_cases hkj : k = j
  · subst k
    simp [move, hj]
  simp [move, hki, hkj]

def shellFilled (lo hi : Fin 7) (a : Occupation) : Prop := a lo = 2 ∧ a hi = 0

instance (lo hi : Fin 7) (a : Occupation) : Decidable (shellFilled lo hi a) := by
  unfold shellFilled
  infer_instance

abbrev OuterFilled (n : ℕ) := {a : Sector n // shellFilled 0 6 a.val}
abbrev Kept (n : ℕ) := {a : OuterFilled n // shellFilled 1 5 a.val.val}
abbrev InnerExcited (n : ℕ) := {a : OuterFilled n // ¬shellFilled 1 5 a.val.val}
abbrev OuterExcited (n : ℕ) := {a : Sector n // ¬shellFilled 0 6 a.val}

noncomputable instance (n : ℕ) : Fintype (Kept n) := Fintype.ofFinite _
noncomputable instance (n : ℕ) : Fintype (InnerExcited n) := Fintype.ofFinite _
noncomputable instance (n : ℕ) : Fintype (OuterExcited n) := Fintype.ofFinite _

/-- Every fixed-particle occupation belongs to exactly one of the three blocks. -/
def split (n : ℕ) : ((Kept n ⊕ InnerExcited n) ⊕ OuterExcited n) ≃ Sector n :=
  (Equiv.sumCongr (Equiv.sumCompl fun a : OuterFilled n => shellFilled 1 5 a.val)
    (Equiv.refl (OuterExcited n))).trans
    (Equiv.sumCompl fun a : Sector n => shellFilled 0 6 a.val)

private theorem grouped_split_injective (n : ℕ) :
    Function.Injective
      (split n ∘ (Equiv.sumAssoc (Kept n) (InnerExcited n) (OuterExcited n)).symm ∘ Sum.inr) :=
  (split n).injective.comp ((Equiv.sumAssoc _ _ _).symm.injective.comp Sum.inr_injective)

def levels (d r s : ℝ) : Fin 7 → ℝ := ![-s, -r, -d, 0, d, r, s]
def freeEnergy (d r s : ℝ) : ℝ := -2 * (s + r + d)

noncomputable def kinetic (d r s : ℝ) (a : Occupation) : ℝ :=
  ∑ i : Fin 7, ((a i).val : ℝ) * levels d r s i

private theorem kinetic_eq (d r s : ℝ) (a : Occupation) :
    kinetic d r s a = freeEnergy d r s +
      s * (2 - (a 0).val + (a 6).val) +
      r * (2 - (a 1).val + (a 5).val) +
      d * (2 - (a 2).val + (a 4).val) := by
  simp [kinetic, freeEnergy, levels, Fin.sum_univ_succ]
  ring

noncomputable def shifted (n : ℕ) (d r s g z : ℝ) : Matrix (Sector n) (Sector n) ℝ :=
  fun i j => if i = j then kinetic d r s i.val - g * pairNumber i.val - z
    else if Hop i.val j.val then -g else 0

noncomputable def hamiltonian (n : ℕ) (d r s g : ℝ) : Matrix (Sector n) (Sector n) ℝ :=
  shifted n d r s g 0

theorem shifted_eq (n : ℕ) (d r s g z : ℝ) :
    shifted n d r s g z = hamiltonian n d r s g - z • 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [shifted, hamiltonian]
  · simp [shifted, hamiltonian, Matrix.one_apply_ne hij, hij]

theorem hamiltonian_symmetric (n : ℕ) (d r s g : ℝ) (i j : Sector n) :
    hamiltonian n d r s g i j = hamiltonian n d r s g j i := by
  by_cases hij : i = j
  · subst j
    rfl
  have hh : Hop i.val j.val ↔ Hop j.val i.val := ⟨Hop.reverse, Hop.reverse⟩
  simp [hamiltonian, shifted, hij, Ne.symm hij, hh]

noncomputable def blockedMatrix (n : ℕ) (d r s g z : ℝ) :=
  (shifted n d r s g z).submatrix (split n) (split n)

private theorem shell_weight_nonneg (a : Occupation) (lo hi : Fin 7) :
    (0 : ℝ) ≤ 2 - (a lo).val + (a hi).val := by
  have hlo : (a lo).val ≤ 2 := by omega
  exact_mod_cast (show (0 : ℤ) ≤ 2 - ((a lo).val : ℤ) + (a hi).val by omega)

private theorem shell_weight_pos (a : Occupation) (lo hi : Fin 7) (h : ¬ shellFilled lo hi a) :
    (1 : ℝ) ≤ 2 - (a lo).val + (a hi).val := by
  have hlo : (a lo).val ≤ 2 := by omega
  have h' : ¬ ((a lo).val = 2 ∧ (a hi).val = 0) := by
    intro hval
    exact h ⟨Fin.ext hval.1, Fin.ext hval.2⟩
  exact_mod_cast (show (1 : ℤ) ≤ 2 - ((a lo).val : ℤ) + (a hi).val by omega)

private theorem kinetic_gap {d r s : ℝ} (hd : 0 ≤ d) (hdr : d ≤ r) (hrs : r ≤ s)
    (a : Occupation) (h : ¬shellFilled 0 6 a ∨ ¬shellFilled 1 5 a) :
    freeEnergy d r s + r ≤ kinetic d r s a := by
  rw [kinetic_eq]
  have hr : 0 ≤ r := hd.trans hdr
  have hs : 0 ≤ s := hr.trans hrs
  have hcen := mul_nonneg hd (shell_weight_nonneg a 2 4)
  rcases h with ho | hi
  · have h1 := mul_le_mul_of_nonneg_left (shell_weight_pos a 0 6 ho) hs
    have h2 := mul_nonneg hr (shell_weight_nonneg a 1 5)
    linarith
  · have h1 := mul_nonneg hs (shell_weight_nonneg a 0 6)
    have h2 := mul_le_mul_of_nonneg_left (shell_weight_pos a 1 5 hi) hr
    linarith

private theorem pairNumber_le (a : Occupation) : pairNumber a ≤ 7 := by
  calc
    pairNumber a ≤ ∑ _ : Fin 7, (1 : ℕ) := Finset.sum_le_sum (by intro i _; split <;> omega)
    _ = 7 := by simp

private theorem neighbor_count {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → Occupation) (ha : Function.Injective a) (i : ι) :
    ((Finset.univ.erase i).filter (fun j => Hop (a i) (a j))).card ≤ 49 := by
  classical
  let neighbors := (Finset.univ.erase i).filter (fun j => Hop (a i) (a j))
  let targets := (Finset.univ : Finset (Fin 7 × Fin 7)).image
    (fun ij => move (a i) ij.1 ij.2)
  have hm (j : {j // j ∈ neighbors}) : a j.val ∈ targets := by
    obtain ⟨source, dest, _, _, he⟩ := (Finset.mem_filter.mp j.property).2
    exact Finset.mem_image.mpr ⟨(source, dest), Finset.mem_univ _, he.symm⟩
  let f (j : {j // j ∈ neighbors}) : {b // b ∈ targets} := ⟨a j.val, hm j⟩
  have hinj : Function.Injective f := fun _ _ he => Subtype.ext (ha (congrArg Subtype.val he))
  have hcard := Fintype.card_le_of_injective f hinj
  rw [Fintype.card_coe, Fintype.card_coe] at hcard
  exact hcard.trans ((Finset.card_image_le).trans (by simp))

private theorem restriction_isUnit {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (idx : ι → Sector n) (hinj : Function.Injective idx)
    {d r s g z : ℝ} (hd : 0 ≤ d) (hdr : d ≤ r) (hrs : r ≤ s) (hg : 0 ≤ g)
    (hz : z < freeEnergy d r s + r - 56 * g)
    (hhigh : ∀ i : ι, ¬shellFilled 0 6 (idx i).val ∨ ¬shellFilled 1 5 (idx i).val) :
    IsUnit ((shifted n d r s g z).submatrix idx idx) := by
  classical
  apply (Matrix.isUnit_iff_isUnit_det _).2
  apply isUnit_iff_ne_zero.2
  apply det_ne_zero_of_sum_row_lt_diag
  intro i
  have hp : (pairNumber (idx i).val : ℝ) ≤ 7 := by exact_mod_cast pairNumber_le (idx i).val
  have hdiag : 49 * g < kinetic d r s (idx i).val - g * pairNumber (idx i).val - z := by
    have hkin := kinetic_gap hd hdr hrs (idx i).val (hhigh i)
    linarith [mul_le_mul_of_nonneg_left hp hg]
  have hsum : ∑ j ∈ Finset.univ.erase i,
      ‖(shifted n d r s g z).submatrix idx idx i j‖ ≤ 49 * g := by
    have he (j : ι) (hj : j ∈ Finset.univ.erase i) :
        ‖(shifted n d r s g z).submatrix idx idx i j‖ =
          if Hop (idx i).val (idx j).val then g else 0 := by
      have hij : idx i ≠ idx j := fun h => (Finset.ne_of_mem_erase hj) (hinj h).symm
      by_cases hh : Hop (idx i).val (idx j).val <;> simp [submatrix, shifted, hij, hh, Real.norm_eq_abs, abs_of_nonneg hg]
    rw [Finset.sum_congr rfl he, ← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul]
    have hc := neighbor_count (fun j => (idx j).val) (Subtype.val_injective.comp hinj) i
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hg
  apply hsum.trans_lt
  simpa [submatrix, shifted, Real.norm_eq_abs,
    abs_of_pos ((mul_nonneg (by norm_num : (0 : ℝ) ≤ 49) hg).trans_lt hdiag)] using hdiag

/-- A single analytic window guarantees both pivots. The full discarded block
is nonsingular throughout the window, including energies at or below the free
reference whenever `56 * g < r`. -/
theorem shell_pivots (n : ℕ) {d r s g z : ℝ}
    (hd : 0 ≤ d) (hdr : d ≤ r) (hrs : r ≤ s) (hg : 0 ≤ g)
    (hz : z < freeEnergy d r s + r - 56 * g) :
    IsUnit (blockedMatrix n d r s g z).toBlocks₂₂ ∧
    IsUnit (schur (blockedMatrix n d r s g z)).toBlocks₂₂ := by
  let M := blockedMatrix n d r s g z
  have houter : IsUnit M.toBlocks₂₂ :=
    restriction_isUnit n (split n ∘ Sum.inr) ((split n).injective.comp Sum.inr_injective)
      hd hdr hrs hg hz (fun i => Or.inl i.property)
  have hall : IsUnit (groupEliminated M).toBlocks₂₂ :=
    restriction_isUnit n _ (grouped_split_injective n) hd hdr hrs hg hz
      (fun i => match i with | .inl j => Or.inr j.property | .inr j => Or.inl j.property)
  exact ⟨houter, (grouped_pivot_isUnit_iff M houter).1 hall⟩

/-- Eliminating the outer shell and then the inner shell is exactly the
one-step elimination of both shells at the same spectral parameter. -/
theorem exact_shell_composition (n : ℕ) {d r s g z : ℝ}
    (hd : 0 ≤ d) (hdr : d ≤ r) (hrs : r ≤ s) (hg : 0 ≤ g)
    (hz : z < freeEnergy d r s + r - 56 * g) :
    schur (schur (blockedMatrix n d r s g z)) =
      schur (groupEliminated (blockedMatrix n d r s g z)) := by
  exact schur_compose _ (shell_pivots n hd hdr hrs hg hz).1 (shell_pivots n hd hdr hrs hg hz).2

/-- Throughout the window the successive effective equation has a nonzero
solution exactly at an eigenvalue of the primitive fixed-number Hamiltonian. -/
theorem exact_shell_eigenvalue (n : ℕ) {d r s g z : ℝ}
    (hd : 0 ≤ d) (hdr : d ≤ r) (hrs : r ≤ s) (hg : 0 ≤ g)
    (hz : z < freeEnergy d r s + r - 56 * g) :
    (∃ x : Kept n → ℝ, x ≠ 0 ∧ schur (schur (blockedMatrix n d r s g z)) *ᵥ x = 0) ↔
      ∃ v : Sector n → ℝ, v ≠ 0 ∧ hamiltonian n d r s g *ᵥ v = z • v := by
  obtain ⟨h₁, h₂⟩ := shell_pivots n hd hdr hrs hg hz
  let M := blockedMatrix n d r s g z
  refine (schur_kernel_iff (schur M) h₂).trans ((schur_kernel_iff M h₁).trans ?_)
  change (∃ v, v ≠ 0 ∧ (shifted n d r s g z).submatrix (split n) (split n) *ᵥ v = 0) ↔ _
  refine (submatrix_kernel_iff (shifted n d r s g z) (split n)).trans ?_
  simp only [shifted_eq, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero]

/-- The weak-coupling regime of the five-orbital experiment gives a
nonempty verified window for all seven-orbital radii above the central spacing. -/
theorem weak_coupling_window {d r s g z : ℝ} (hd : 0 < d) (hdr : d ≤ r)
    (hg : g ≤ d / 1000) (hz : z ≤ freeEnergy d r s) :
    z < freeEnergy d r s + r - 56 * g := by
  linarith

/-- A normalized trial state with the three lowest levels paired and the
central occupation set to 0, 1, or 2. This bounds the variational ground
energy by the free reference in each of the sectors used for parity. -/
theorem reference_trial (k : Fin 3) (d r s : ℝ) {g : ℝ} (hg : 0 ≤ g) :
    ∃ v : Sector (6 + k.val) → ℝ, normSq v = 1 ∧
      v ⬝ᵥ (hamiltonian (6 + k.val) d r s g *ᵥ v) ≤ freeEnergy d r s := by
  let a : Occupation := ![2, 2, 2, k, 0, 0, 0]
  have ha : electronCount a = 6 + k.val := by
    simp [electronCount, a, Fin.sum_univ_succ]
    omega
  let i : Sector (6 + k.val) := ⟨a, ha⟩
  let v : Sector (6 + k.val) → ℝ := Pi.single i 1
  have hdiag : hamiltonian (6 + k.val) d r s g i i ≤ freeEnergy d r s := by
    have hkin : kinetic d r s a = freeEnergy d r s := by simp [kinetic_eq, a]
    simp only [hamiltonian, shifted, ite_true, sub_zero]
    change kinetic d r s a - g * pairNumber a ≤ freeEnergy d r s
    rw [hkin]
    exact sub_le_self _ (mul_nonneg hg (Nat.cast_nonneg _))
  refine ⟨v, ?_, ?_⟩
  · simp [v, normSq, Pi.single_apply]
  · change Pi.single i 1 ⬝ᵥ (hamiltonian (6 + k.val) d r s g *ᵥ Pi.single i 1) ≤ _
    rw [Matrix.mulVec_single_one]
    simpa [dotProduct, Pi.single_apply, Matrix.col] using hdiag

/-- Every variational lower bound, in particular the ground energy, is within
the verified window for the parity sectors when `56 * g < r`. -/
theorem parity_ground_in_window (k : Fin 3) (d r s : ℝ) {g z : ℝ} (hg : 0 ≤ g)
    (hr : 56 * g < r)
    (hlower : ∀ v : Sector (6 + k.val) → ℝ,
      z * normSq v ≤ v ⬝ᵥ (hamiltonian (6 + k.val) d r s g *ᵥ v)) :
    z < freeEnergy d r s + r - 56 * g := by
  obtain ⟨v, hv, he⟩ := reference_trial k d r s hg
  have hz := hlower v
  rw [hv, mul_one] at hz
  linarith

end Grain.TwoShell
