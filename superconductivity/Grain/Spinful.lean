import Grain.PhononBridge

/-! The electron Hilbert space and the one-body vertices of the grain. -/

namespace Grain.Phonon

open TwoShell
open scoped BigOperators

abbrev Slot := Fin 7 × Fin 2
abbrev SpinConfig := Slot → Bool
abbrev Bond := {ij : Fin 7 × Fin 7 // ij.1 < ij.2}
abbrev Mode := Bond ⊕ Fin 7

def occupationOf (a : SpinConfig) : Occupation := fun i =>
  ⟨(a (i, 0)).toNat + (a (i, 1)).toNat, by
    cases a (i, 0) <;> cases a (i, 1) <;> decide⟩

abbrev SpinSector (n : ℕ) := {a : SpinConfig // electronCount (occupationOf a) = n}

def toOccupation {n : ℕ} (a : SpinSector n) : Sector n :=
  ⟨occupationOf a.val, a.property⟩

private def slotNumber (s : Slot) : ℕ := 2 * s.1.val + s.2.val

def hopPerm {n : ℕ} (b : Bond) (σ : Fin 2) : Equiv.Perm (SpinSector n) :=
  let swap := Equiv.swap (b.val.1, σ) (b.val.2, σ)
  have count (a : SpinConfig) :
      electronCount (occupationOf (a ∘ swap)) = electronCount (occupationOf a) := by
    have total (v : SpinConfig) :
        electronCount (occupationOf v) = ∑ s : Slot, (v s).toNat := by
      simp [electronCount, occupationOf, Fintype.sum_prod_type, Fin.sum_univ_two]
    rw [total, total]
    exact Equiv.sum_comp swap (fun s => (a s).toNat)
  { toFun := fun a => ⟨a.val ∘ swap, (count a.val).trans a.property⟩
    invFun := fun a => ⟨a.val ∘ swap, (count a.val).trans a.property⟩
    left_inv := fun a => Subtype.ext (funext fun s => by simp [swap, Function.comp_apply])
    right_inv := fun a => Subtype.ext (funext fun s => by simp [swap, Function.comp_apply]) }

/-- Signed hopping between the two endpoints in the site-ordered Fock basis. -/
def hopSign {n : ℕ} (b : Bond) (σ : Fin 2) (a : SpinSector n) : ℤ :=
  if a.val (b.val.1, σ) = a.val (b.val.2, σ) then 0 else
    (-1) ^ (∑ s : Slot,
      if slotNumber (b.val.1, σ) < slotNumber s ∧ slotNumber s < slotNumber (b.val.2, σ)
      then (a.val s).toNat else 0)

theorem hopSign_perm {n : ℕ} (b : Bond) (σ : Fin 2) (a : SpinSector n) :
    hopSign b σ (hopPerm b σ a) = hopSign b σ a := by
  let i : Slot := (b.val.1, σ)
  let j : Slot := (b.val.2, σ)
  have hsum :
      (∑ s : Slot, if slotNumber i < slotNumber s ∧ slotNumber s < slotNumber j
        then (a.val (Equiv.swap i j s)).toNat else 0) =
      ∑ s : Slot, if slotNumber i < slotNumber s ∧ slotNumber s < slotNumber j
        then (a.val s).toNat else 0 := by
    apply Finset.sum_congr rfl
    intro s _
    split
    · rename_i hs
      have hsi : s ≠ i := fun h => (ne_of_lt hs.1) (congrArg slotNumber h.symm)
      have hsj : s ≠ j := fun h => (ne_of_lt hs.2) (congrArg slotNumber h)
      rw [Equiv.swap_apply_of_ne_of_ne hsi hsj]
    · rfl
  change (if a.val (Equiv.swap i j i) = a.val (Equiv.swap i j j) then 0 else
    (-1 : ℤ) ^ (∑ s : Slot, if slotNumber i < slotNumber s ∧ slotNumber s < slotNumber j
      then (a.val (Equiv.swap i j s)).toNat else 0)) =
    (if a.val i = a.val j then 0 else (-1 : ℤ) ^
      (∑ s : Slot, if slotNumber i < slotNumber s ∧ slotNumber s < slotNumber j
        then (a.val s).toNat else 0))
  simp only [Equiv.swap_apply_left, Equiv.swap_apply_right, hsum,
    show a.val j = a.val i ↔ a.val i = a.val j from eq_comm]

def kineticDiagonal (r s : ℚ) {n : ℕ} (a : SpinSector n) : ℚ :=
  ∑ i : Fin 7, ((occupationOf a.val i).val : ℚ) * rationalLevels r s i

noncomputable def kineticForm (r s : ℚ) {n : ℕ} (x : SpinSector n → ℝ) : ℝ :=
  ∑ a, (kineticDiagonal r s a : ℝ) * x a ^ 2

noncomputable def vertex {n : ℕ} (m : Mode) (x : SpinSector n → ℝ) (a : SpinSector n) : ℝ :=
  match m with
  | .inl b => ∑ σ : Fin 2, (hopSign b σ a : ℝ) * x (hopPerm b σ a)
  | .inr i => ((occupationOf a.val i).val : ℝ) * x a

theorem vertex_symmetric {n : ℕ} (m : Mode) (x y : SpinSector n → ℝ) :
    inner x (vertex m y) = inner (vertex m x) y := by
  cases m with
  | inr i =>
    unfold inner
    apply Finset.sum_congr rfl
    intro a _
    simp [vertex]
    ring
  | inl b =>
    simp only [inner, vertex, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm, Finset.sum_comm (f := fun a σ =>
      (hopSign b σ a : ℝ) * x (hopPerm b σ a) * y a)]
    apply Finset.sum_congr rfl
    intro σ _
    rw [← Equiv.sum_comp (hopPerm b σ) (fun a => (hopSign b σ a : ℝ) * x (hopPerm b σ a) * y a)]
    apply Finset.sum_congr rfl
    intro a _
    have involution : hopPerm b σ (hopPerm b σ a) = a :=
      (hopPerm b σ).left_inv a
    rw [hopSign_perm, involution]
    ring

private theorem hopSign_sq_le {n : ℕ} (b : Bond) (σ : Fin 2) (a : SpinSector n) :
    (hopSign b σ a : ℝ) ^ 2 ≤ 1 := by
  unfold hopSign
  split
  · norm_num
  · push_cast
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num

theorem vertex_norm_le {n : ℕ} (m : Mode) (x : SpinSector n → ℝ) :
    normSq (vertex m x) ≤ 4 * normSq x := by
  cases m with
  | inr i =>
    unfold normSq
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a _
    have hi : ((occupationOf a.val i).val : ℝ) ≤ 2 := by
      exact_mod_cast (show (occupationOf a.val i).val ≤ 2 by omega)
    simp only [vertex, mul_pow]
    exact mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg _)
  | inl b =>
    unfold normSq
    have term (σ : Fin 2) (a : SpinSector n) :
        ((hopSign b σ a : ℝ) * x (hopPerm b σ a)) ^ 2 ≤ x (hopPerm b σ a) ^ 2 := by
      rw [mul_pow]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hopSign_sq_le b σ a) (sq_nonneg _)
    calc
      _ ≤ ∑ a, 2 * (x (hopPerm b 0 a) ^ 2 + x (hopPerm b 1 a) ^ 2) := by
        apply Finset.sum_le_sum
        intro a _
        simp only [vertex, Fin.sum_univ_two]
        nlinarith only [term 0 a, term 1 a,
          sq_nonneg ((hopSign b 0 a : ℝ) * x (hopPerm b 0 a) -
            (hopSign b 1 a : ℝ) * x (hopPerm b 1 a))]
      _ = _ := by
        simp only [← Finset.mul_sum, Finset.sum_add_distrib,
          Equiv.sum_comp (hopPerm b 0) (fun a => x a ^ 2),
          Equiv.sum_comp (hopPerm b 1) (fun a => x a ^ 2)]
        ring

theorem vertexNorm_le {n : ℕ} (x : SpinSector n → ℝ) :
    vertexNorm vertex x ≤ 112 * normSq x := by
  have card : Fintype.card Mode = 28 := by decide +kernel
  calc
    vertexNorm vertex x ≤ ∑ _ : Mode, 4 * normSq x :=
      Finset.sum_le_sum fun m _ => vertex_norm_le m x
    _ = _ := by simp [card]; ring

end Grain.Phonon
