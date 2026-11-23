import Grain.GroundResolvent
import Grain.ParityMatching
import Grain.ShellCertificate

/-! Occupation-level inputs for the scalar parity error budget. -/

namespace Grain.ParityMatching

open ResolventRemainder
open scoped BigOperators

private def gapOf {ι τ : Type} (A : ι → ι → ℚ) (idx : Option τ → ι) (i : τ) : ℚ :=
  A (idx (some i)) (idx (some i)) - A (idx none) (idx none)

private def hopWeight {ι : Type} (edge : ι → ι → Prop) [DecidableRel edge] (i j : ι) : ℚ :=
  if edge i j then 1 else 0

private def sectorPolynomial {ι τ : Type} [Fintype τ]
    (A : ι → ι → ℚ) (idx : Option τ → ι) (v : τ → ℚ) (T : τ → τ → ℚ) (g : ℚ) : ℚ :=
  let hops := Finset.univ.filter fun i => v i ≠ 0
  let u := fun i => v i / gapOf A idx i
  A (idx none) (idx none) - g ^ 2 * (∑ i ∈ hops, v i * u i) -
    g ^ 3 * ∑ i ∈ hops, ∑ j ∈ hops, u i * T i j * u j

private theorem sectorPolynomial_eq {ι τ : Type} [Fintype τ]
    (A : ι → ι → ℚ) (idx : Option τ → ι) (v : τ → ℚ) (T : τ → τ → ℚ) (g : ℚ) :
    sectorPolynomial A idx v T g =
      let u := fun i => v i / gapOf A idx i
      let w := fun i => Grain.action T u i / gapOf A idx i
      A (idx none) (idx none) - g ^ 2 * (∑ i, v i * u i) - g ^ 3 * (∑ i, v i * w i) := by
  dsimp only [sectorPolynomial]
  have restrict (f : τ → ℚ) (hf : ∀ i, v i = 0 → f i = 0) :
      (∑ i ∈ Finset.univ.filter (fun i => v i ≠ 0), f i) = ∑ i, f i := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    exact hf i (by simpa using hi)
  rw [restrict (fun i => v i * (v i / gapOf A idx i)) (by simp +contextual)]
  congr 2
  rw [restrict _ (by simp +contextual)]
  apply Finset.sum_congr rfl
  intro i _
  rw [restrict _ (by simp +contextual)]
  simp only [Grain.action, div_eq_mul_inv]
  rw [Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- Parity evaluated on the diagonal, two-hop and three-hop terms of each sector. -/
def polynomialParity (p : Fin 3 → ℚ) : ℚ := p 1 - (p 0 + p 2) / 2

section Full

open TwoShell

def innerRadius (far : Bool) : ℚ := if far then 5 else 2
def outerRadius (far : Bool) : ℚ := if far then 14 else 6

private def fullH (r s : Bool) (c : Fin 3) :=
  ratH (innerRadius r) (outerRadius s) (6 + c.val)

noncomputable def fullEnergy (r s : Bool) (c : Fin 3) : ℝ := ground (fullH r s c)

noncomputable def fullParity (r s : Bool) : ℝ :=
  fullEnergy r s 1 - (fullEnergy r s 0 + fullEnergy r s 2) / 2

private def fullReference (c : Fin 3) : Occupation := ![2, 2, 2, c, 0, 0, 0]

private theorem fullReference_count (c : Fin 3) : electronCount (fullReference c) = 6 + c.val := by
  fin_cases c <;> decide +kernel

private theorem fullReference_active (c : Fin 3) : active (6 + c.val) (fullReference c) := by
  fin_cases c <;> decide +kernel

/-- Ternary occupation codes for the tail. The enumeration is checked below. -/
private def fullTailCodes : Fin 3 → List ℕ
  | 0 => [62, 74, 78, 170, 182, 186, 218, 222, 234, 494, 506, 510, 542, 546, 558, 650, 654, 666, 702, 1466, 1478, 1482, 1514, 1518, 1530, 1622, 1626, 1638, 1674, 1946, 1950, 1962, 1998, 2106]
  | 1 => [197, 209, 213, 521, 533, 537, 677, 681, 693, 1493, 1505, 1509, 1649, 1653, 1665, 1973, 1977, 1989, 2133]
  | 2 => [188, 224, 236, 240, 512, 548, 560, 564, 656, 668, 672, 704, 708, 720, 1484, 1520, 1532, 1536, 1628, 1640, 1644, 1676, 1680, 1692, 1952, 1964, 1968, 2000, 2004, 2016, 2108, 2112, 2124, 2160]

private def fullTail (c : Fin 3) : List Occupation := (fullTailCodes c).map decode

set_option maxRecDepth 10000 in
private theorem fullTail_enumeration (c : Fin 3) :
    fullTail c = ((List.range 2187).map decode).filter (fun a =>
      decide (electronCount a = 6 + c.val ∧ active (6 + c.val) a ∧ a ≠ fullReference c)) := by
  fin_cases c <;> decide +kernel

private abbrev FullTail (c : Fin 3) := Fin (fullTail c).length

private theorem fullTail_mem {c : Fin 3} {a : Occupation} :
    a ∈ fullTail c ↔ electronCount a = 6 + c.val ∧ active (6 + c.val) a ∧ a ≠ fullReference c := by
  have ha : a ∈ (List.range 2187).map decode :=
    for_all_occupations (fun k => List.mem_map.mpr ⟨k.val, List.mem_range.mpr k.isLt, rfl⟩) a
  simp [fullTail_enumeration c, ha]

private def fullIndex (c : Fin 3) : Option (FullTail c) → Sector (6 + c.val)
  | none => ⟨fullReference c, fullReference_count c⟩
  | some i => ⟨(fullTail c).get i, ((fullTail_mem (c := c)).mp (List.getElem_mem (l := fullTail c) i.isLt)).1⟩

private theorem fullIndex_injective (c : Fin 3) : Function.Injective (fullIndex c) := by
  have hnd : (fullTail c).Nodup := by fin_cases c <;> decide +kernel
  intro i j he
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some j => exact (((fullTail_mem (c := c)).mp (List.getElem_mem (l := fullTail c) j.isLt)).2.2
        (congrArg Subtype.val he).symm).elim
  | some i =>
    cases j with
    | none => exact (((fullTail_mem (c := c)).mp (List.getElem_mem (l := fullTail c) i.isLt)).2.2
        (congrArg Subtype.val he)).elim
    | some j =>
      congr 1
      exact Fin.ext (hnd.getElem_inj_iff.mp (congrArg Subtype.val he))

private theorem fullIndex_range (c : Fin 3) (a : Sector (6 + c.val)) :
    a ∈ Set.range (fullIndex c) ↔ active (6 + c.val) a.val := by
  constructor
  · rintro ⟨i, rfl⟩
    cases i with
    | none => exact fullReference_active c
    | some j => exact ((fullTail_mem (c := c)).mp (List.getElem_mem (l := fullTail c) j.isLt)).2.1
  · intro ha
    by_cases h : a.val = fullReference c
    · exact ⟨none, Subtype.ext h.symm⟩
    · obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp ((fullTail_mem (c := c)).mpr ⟨a.property, ha, h⟩)
      exact ⟨some ⟨j, hj⟩, Subtype.ext he⟩

private theorem hop_active {n : ℕ} {a b : Occupation} (h : Hop a b) (ha : active n a) :
    active n b := by
  obtain ⟨i, j, hi, hj, rfl⟩ := h
  intro k
  have hk : move a i j k = 1 ↔ a k = 1 := by
    by_cases hki : k = i
    · subst k
      simp [move, hi]
    · by_cases hkj : k = j
      · subst k
        simp [move, hki, hj]
      · simp [move, hki, hkj]
  exact hk.trans (ha k)

private theorem full_symm (r s : Bool) (c : Fin 3) (i j : Sector (6 + c.val)) :
    fullH r s c i j = fullH r s c j i := by
  unfold fullH
  exact_mod_cast (ratH_cast _ _ _ i j).trans ((hamiltonian_symmetric _ _ _ _ _ i j).trans
    (ratH_cast _ _ _ j i).symm)

private theorem full_sign (r s : Bool) (c : Fin 3) (i j : Sector (6 + c.val)) (h : i ≠ j) :
    fullH r s c i j ≤ 0 := by
  by_cases hh : Hop i.val j.val <;> norm_num [fullH, ratH, h, hh, coupling]

private theorem full_cross (r s : Bool) (c : Fin 3) (i : Option (FullTail c))
    (j : Sector (6 + c.val)) (hj : j ∉ Set.range (fullIndex c)) :
    fullH r s c (fullIndex c i) j = 0 := by
  have hne : fullIndex c i ≠ j := fun h => hj ⟨i, h⟩
  have hh : ¬ Hop (fullIndex c i).val j.val := fun h =>
    hj ((fullIndex_range c j).mpr (hop_active h ((fullIndex_range c _).mp ⟨i, rfl⟩)))
  simp [fullH, ratH, hne, hh]

private theorem kinetic_penalty (r s : ℚ) (a : Occupation) :
    ∑ i, ((a i).val : ℚ) * rationalLevels r s i =
      -2 * (s + r + 1) + s * (2 - (a 0).val + (a 6).val) +
      r * (2 - (a 1).val + (a 5).val) + (2 - (a 2).val + (a 4).val) := by
  simp [rationalLevels, Fin.sum_univ_succ]
  ring

private theorem full_inactive_diagonal (r s : Bool) (c : Fin 3) (a : Occupation)
    (hn : electronCount a = 6 + c.val) (ha : ¬ active (6 + c.val) a) :
    TwoShell.diagonal (innerRadius r) (outerRadius s) (fullReference c) <
      TwoShell.diagonal (innerRadius r) (outerRadius s) a - 49 * coupling := by
  have hpairs : pairNumber a ≤ pairNumber (fullReference c) := by
    have hcount : 2 * pairNumber a ≤ electronCount a := by
      simp only [pairNumber, electronCount, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      split
      · rename_i h
        simp [h]
      · simp
    have href : pairNumber (fullReference c) = (6 + c.val) / 2 := by
      fin_cases c <;> decide +kernel
    omega
  have hexc : (a 0 ≠ 2 ∨ a 6 ≠ 0) ∨ (a 1 ≠ 2 ∨ a 5 ≠ 0) ∨ (a 2 ≠ 2 ∨ a 4 ≠ 0) := by
    by_contra! h
    obtain ⟨⟨h₀, h₆⟩, ⟨h₁, h₅⟩, h₂, h₄⟩ := h
    have hcenter : a 3 = c := by
      simp [electronCount, Fin.sum_univ_succ, h₀, h₁, h₂, h₄, h₅, h₆] at hn
      exact Fin.ext (by omega)
    have he : a = fullReference c := by
      funext i
      fin_cases i <;> assumption
    exact ha (he ▸ fullReference_active c)
  let δ := fun lo hi : Fin 7 => (2 : ℚ) - (a lo).val + (a hi).val
  have hδ (lo hi : Fin 7) : 0 ≤ δ lo hi := by
    have hlo := (a lo).isLt
    dsimp [δ]
    exact_mod_cast (show (0 : ℤ) ≤ 2 - ((a lo).val : ℤ) + (a hi).val by omega)
  have hδ' (lo hi : Fin 7) (h : a lo ≠ 2 ∨ a hi ≠ 0) : 1 ≤ δ lo hi := by
    have hne : (a lo).val ≠ 2 ∨ (a hi).val ≠ 0 := h.imp
      (fun hl he => hl (Fin.ext he)) (fun hh he => hh (Fin.ext he))
    have hlo := (a lo).isLt
    dsimp [δ]
    exact_mod_cast (show (1 : ℤ) ≤ 2 - ((a lo).val : ℤ) + (a hi).val by omega)
  have hr : 1 ≤ innerRadius r := by cases r <;> norm_num [innerRadius]
  have hs : 1 ≤ outerRadius s := by cases s <;> norm_num [outerRadius]
  have hkin : 1 ≤ outerRadius s * δ 0 6 + innerRadius r * δ 1 5 + δ 2 4 := by
    have h₀ := mul_le_mul_of_nonneg_right hs (hδ 0 6)
    have h₁ := mul_le_mul_of_nonneg_right hr (hδ 1 5)
    rcases hexc with h | h | h
    · linarith [hδ' 0 6 h, hδ 1 5, hδ 2 4]
    · linarith [hδ' 1 5 h, hδ 0 6, hδ 2 4]
    · linarith [hδ' 2 4 h, hδ 0 6, hδ 1 5]
  have href : ∑ i, (((fullReference c) i).val : ℚ) *
      rationalLevels (innerRadius r) (outerRadius s) i =
        -2 * (outerRadius s + innerRadius r + 1) := by
    rw [kinetic_penalty]
    norm_num [fullReference]
  unfold TwoShell.diagonal
  rw [href, kinetic_penalty]
  have hpair : (pairNumber a : ℚ) ≤ pairNumber (fullReference c) := by exact_mod_cast hpairs
  dsimp [δ] at hkin
  norm_num [coupling]
  linarith

private theorem full_other (r s : Bool) (c : Fin 3) (i : Sector (6 + c.val))
    (hi : i ∉ Set.range (fullIndex c)) :
    fullH r s c (fullIndex c none) (fullIndex c none) < Grain.action (fullH r s c) 1 i := by
  have ha : ¬active (6 + c.val) i.val := fun h => hi ((fullIndex_range c i).mpr h)
  have hh := full_inactive_diagonal r s c i.val i.property ha
  have hsum : (∑ p : Fin 7 × Fin 7, if legal i.val p then (1 : ℚ) else 0) ≤ 49 := by
    exact (Finset.sum_le_sum (fun p _ => by split <;> norm_num)).trans
      (show (∑ _ : Fin 7 × Fin 7, (1 : ℚ)) ≤ 49 by norm_num)
  change ratH _ _ _ _ _ < Grain.action (ratH _ _ _) (fun _ => (1 : ℚ)) i
  rw [sparseAction_eq _ _ (fun _ => 1)]
  simp only [ratH, ite_true, sparseAction]
  change TwoShell.diagonal (innerRadius r) (outerRadius s) (fullReference c) < _
  have hg : 0 ≤ coupling := by norm_num [coupling]
  linarith [mul_le_mul_of_nonneg_left hsum hg]

private def losses (a b : Occupation) : Finset (Fin 7) :=
  Finset.univ.filter (fun i => a i = 2 ∧ b i = 0)

/-- A pair transfer changes exactly one full site to empty and one empty site to full. -/
private theorem hop_iff_losses (a b : Occupation) :
    Hop a b ↔
      (losses a b).card = 1 ∧ (losses b a).card = 1 ∧
      ∀ i, a i = b i ∨ i ∈ losses a b ∨ i ∈ losses b a := by
  constructor
  · rintro ⟨i, j, hi, hj, rfl⟩
    have hne : i ≠ j := by intro h; subst j; simp [hi] at hj
    have h₁ : losses a (move a i j) = {i} := by
      ext k
      simp only [losses, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      rcases eq_or_ne k i with rfl | hk
      · simp [move, hi]
      · rcases eq_or_ne k j with rfl | hk'
        · simp [move, hk]
        · simp [move, hk, hk']; omega
    have h₂ : losses (move a i j) a = {j} := by
      ext k
      simp only [losses, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      rcases eq_or_ne k j with rfl | hk
      · simp [move, hne.symm, hj]
      · rcases eq_or_ne k i with rfl | hk'
        · simp [move, hk]
        · simp [move, hk, hk']; omega
    rw [h₁, h₂]
    refine ⟨by simp, by simp, fun k => ?_⟩
    by_cases hk : k = i <;> by_cases hk' : k = j <;> simp [move, hk, hk']
  · rintro ⟨h₁, h₂, hrest⟩
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp h₁
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp h₂
    have hi' : i ∈ losses a b := by simp [hi]
    have hj' : j ∈ losses b a := by simp [hj]
    have hi' := (Finset.mem_filter.mp hi').2
    have hj' := (Finset.mem_filter.mp hj').2
    have hne : j ≠ i := by intro h; subst j; simp [hi'.1] at hj'
    refine ⟨i, j, hi'.1, hj'.2, funext fun k => ?_⟩
    by_cases hk : k = i
    · subst k
      simp [move, hi'.2]
    · by_cases hk' : k = j
      · subst k
        simp [move, hne, hj'.1]
      · have he : a k = b k := by simpa [hi, hj, hk, hk'] using hrest k
        simp [move, hk, hk', he]

private def fullEdge {n : ℕ} (i j : Sector n) : Prop := Hop i.val j.val

private instance {n : ℕ} : DecidableRel (@fullEdge n) := fun i j =>
  decidable_of_iff _ (hop_iff_losses i.val j.val).symm

private def fullV (c : Fin 3) (i : FullTail c) : ℚ :=
  hopWeight fullEdge (fullIndex c none) (fullIndex c (some i))

private def fullT (c : Fin 3) (i j : FullTail c) : ℚ :=
  if i = j then 0 else hopWeight fullEdge (fullIndex c (some i)) (fullIndex c (some j))

private theorem full_head_entry (r s : Bool) (c : Fin 3) (i : FullTail c) :
    fullH r s c (fullIndex c none) (fullIndex c (some i)) = -coupling * fullV c i := by
  have hne : fullIndex c none ≠ fullIndex c (some i) :=
    fun h => by have hh := fullIndex_injective c h; cases hh
  by_cases h : Hop (fullIndex c none).val (fullIndex c (some i)).val <;>
    simp [fullH, ratH, hne, fullV, hopWeight, fullEdge, h]

private theorem full_tail_entry (r s : Bool) (c : Fin 3) (i j : FullTail c) :
    fullH r s c (fullIndex c (some i)) (fullIndex c (some j)) =
      (if i = j then fullH r s c (fullIndex c none) (fullIndex c none) +
        gapOf (fullH r s c) (fullIndex c) i else 0) - coupling * fullT c i j := by
  by_cases h : i = j
  · subst j
    simp [gapOf, fullT]
  · have hne : fullIndex c (some i) ≠ fullIndex c (some j) :=
      fun he => h (Option.some.inj (fullIndex_injective c he))
    by_cases hh : Hop (fullIndex c (some i)).val (fullIndex c (some j)).val <;>
      simp [fullH, ratH, h, hne, fullT, hopWeight, fullEdge, hh]

def fullSectorPolynomial (r s : Bool) (c : Fin 3) : ℚ :=
  sectorPolynomial (fullH r s c) (fullIndex c) (fullV c) (fullT c) coupling

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem full_hop_bounds (c : Fin 3) :
    (∀ i, ∑ j, |fullT c i j| ≤ 12) ∧ (∀ i, |fullV c i| ≤ 1) ∧ ∑ j, |fullV c j| ≤ 12 := by
  fin_cases c <;> decide +kernel

set_option maxRecDepth 10000 in
private theorem full_gaps (r s : Bool) (c : Fin 3) :
    ∀ i, 2 ≤ gapOf (fullH r s c) (fullIndex c) i := by
  cases r <;> cases s <;> fin_cases c <;> decide +kernel

theorem full_sector_polynomial_error (r s : Bool) (c : Fin 3) :
    |fullEnergy r s c - (fullSectorPolynomial r s c : ℝ)| ≤
      budget 2 (1 / 100) 12 12 := by
  obtain ⟨hb, hv, hn⟩ := full_hop_bounds c
  have he := ground_remainder (fullH r s c) (fullIndex c) (gapOf (fullH r s c) (fullIndex c))
    (fullV c) (fullT c) (g := coupling) (full_symm r s c) (full_sign r s c)
    (fullIndex_injective c) (full_cross r s c) (full_other r s c) (full_head_entry r s c)
    (full_tail_entry r s c) (by norm_num [coupling]) (by norm_num) (by norm_num [coupling])
    (by norm_num) (by norm_num) (full_gaps r s c) hb hv hn
  simpa only [fullEnergy, fullSectorPolynomial, sectorPolynomial_eq, coupling,
    Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] using he

end Full

def retainedSize (c : Fin 3) : ℕ := if c = 1 then 7 else 6

private def digits (code : ℕ) (i : Fin 3) : ℕ := code / 3^i.val % 3

private def codes (c : Fin 3) :=
  (List.range 27).filter fun code => (∑ i : Fin 3, digits code i) == 2 + c.val

private theorem codes_length (c : Fin 3) : (codes c).length = retainedSize c := by
  fin_cases c <;> decide +kernel

private def occ (c : Fin 3) (j : Fin (retainedSize c)) :=
  digits ((codes c)[j.val]'(by rw [codes_length]; exact j.isLt))

private def transfer (a b : Fin 3 → ℕ) : Prop :=
  ∃ i j : Fin 3, a i = 2 ∧ a j = 0 ∧
    ∀ k : Fin 3, b k = (if k = i then 0 else if k = j then 2 else a k)

private instance (a b : Fin 3 → ℕ) : Decidable (transfer a b) := by
  unfold transfer
  infer_instance

def rationalStrength (r s : Bool) : ℚ :=
  let x : ℚ := if r then 1/5 else 1/2
  let y : ℚ := if s then 1/14 else 1/6
  cubicMatchedCoupling (1/100) (x+y) (x^2+y^2)

def retainedH (r s : Bool) (c : Fin 3) (i j : Fin (retainedSize c)) : ℚ :=
  let a := occ c i
  let g := rationalStrength r s
  if i = j then (a 2 : ℚ) - a 0 - g * (∑ k : Fin 3, if a k = 2 then 1 else 0)
  else if transfer a (occ c j) then -g else 0

noncomputable def retainedParity (r s : Bool) : ℝ :=
  ground (retainedH r s 1) - (ground (retainedH r s 0) + ground (retainedH r s 2)) / 2

private def retainedActive (c : Fin 3) (i : Fin (retainedSize c)) : Prop :=
  ∀ j : Fin 3, occ c i j = 1 ↔ c = 1 ∧ j = 1

private instance (c : Fin 3) (i : Fin (retainedSize c)) : Decidable (retainedActive c i) := by
  unfold retainedActive
  infer_instance

private def retainedHead (c : Fin 3) : Fin (retainedSize c) :=
  ⟨0, by unfold retainedSize; split <;> decide⟩

private def retainedTail (c : Fin 3) : List (Fin (retainedSize c)) :=
  (List.finRange (retainedSize c)).filter fun i => decide (retainedActive c i ∧ i ≠ retainedHead c)

private abbrev RetainedTail (c : Fin 3) := Fin (retainedTail c).length

private def retainedIndex (c : Fin 3) : Option (RetainedTail c) → Fin (retainedSize c)
  | none => retainedHead c
  | some i => (retainedTail c).get i

private theorem retainedIndex_injective (c : Fin 3) : Function.Injective (retainedIndex c) := by
  change ∀ i j, retainedIndex c i = retainedIndex c j → i = j
  fin_cases c <;> decide +kernel

private def retainedEdge (c : Fin 3) (i j : Fin (retainedSize c)) : Prop :=
  i ≠ j ∧ transfer (occ c i) (occ c j)

private instance (c : Fin 3) : DecidableRel (retainedEdge c) := fun i j =>
  inferInstanceAs (Decidable (i ≠ j ∧ transfer (occ c i) (occ c j)))

private def retainedV (c : Fin 3) (i : RetainedTail c) : ℚ :=
  hopWeight (retainedEdge c) (retainedIndex c none) (retainedIndex c (some i))

private def retainedT (c : Fin 3) (i j : RetainedTail c) : ℚ :=
  hopWeight (retainedEdge c) (retainedIndex c (some i)) (retainedIndex c (some j))

def retainedSectorPolynomial (r s : Bool) (c : Fin 3) : ℚ :=
  sectorPolynomial (retainedH r s c) (retainedIndex c) (retainedV c) (retainedT c)
    (rationalStrength r s)

private def retainedBlockChecks (r s : Bool) (c : Fin 3) : Prop :=
  let A := retainedH r s c
  let idx := retainedIndex c
  let g := rationalStrength r s
  (∀ i j, A i j = A j i) ∧
  (∀ i j, i ≠ j → A i j ≤ 0) ∧
  (∀ i j, (∀ k, idx k ≠ j) → A (idx i) j = 0) ∧
  (∀ i, (∀ k, idx k ≠ i) → A (idx none) (idx none) < Grain.action A 1 i) ∧
  (∀ i, A (idx none) (idx (some i)) = -g * retainedV c i) ∧
  (∀ i j, A (idx (some i)) (idx (some j)) =
    (if i = j then A (idx none) (idx none) + gapOf A idx i else 0) - g * retainedT c i j) ∧
  0 < g ∧ g * 2 < 2 ∧
  (∀ i, 2 ≤ gapOf A idx i) ∧
  (∀ i, ∑ j, |retainedT c i j| ≤ 2) ∧
  (∀ i, |retainedV c i| ≤ 1) ∧ ∑ j, |retainedV c j| ≤ 2

private instance (r s : Bool) (c : Fin 3) : Decidable (retainedBlockChecks r s c) := by
  unfold retainedBlockChecks
  infer_instance

set_option maxHeartbeats 0 in
private theorem retained_block_checks (r s : Bool) (c : Fin 3) : retainedBlockChecks r s c := by
  cases r <;> cases s <;> fin_cases c <;> decide +kernel

theorem retained_sector_polynomial_error (r s : Bool) (c : Fin 3) :
    |ground (retainedH r s c) - (retainedSectorPolynomial r s c : ℝ)| ≤
      budget 2 (rationalStrength r s : ℝ) 2 2 := by
  obtain ⟨hs, hn, hc, ho, hh, ht, hg, hsmall, hd, hb, hv, hV⟩ := retained_block_checks r s c
  have he := ground_remainder (retainedH r s c) (retainedIndex c)
    (gapOf (retainedH r s c) (retainedIndex c)) (retainedV c) (retainedT c)
    hs hn (retainedIndex_injective c)
    (fun i j hj => hc i j (fun k hk => hj ⟨k, hk⟩))
    (fun i hi => ho i (fun k hk => hi ⟨k, hk⟩)) hh ht hg (by norm_num) hsmall
    (by norm_num) (by norm_num) hd hb hv hV
  simpa only [retainedSectorPolynomial, sectorPolynomial_eq, Rat.cast_ofNat] using he

end Grain.ParityMatching
