import Grain.Spinful

/-! The electronic comparison obtained by completing the harmonic square.
The active rows are checked by composing the microscopic one-electron hops. -/

namespace Grain.Phonon

open TwoShell
open scoped BigOperators

def spinConfig (down : Bool) (a : Occupation) : SpinConfig := fun (i, σ) =>
  a i == 2 || (a i == 1 && σ == if i = 3 && down then 1 else 0)

@[simp] theorem occupationOf_spinConfig (down : Bool) (a : Occupation) :
    occupationOf (spinConfig down a) = a := by
  funext i
  apply Fin.ext
  let σ : Fin 2 := if i = 3 && down then 1 else 0
  change (a i == 2 || (a i == 1 && (0 : Fin 2) == σ)).toNat +
    (a i == 2 || (a i == 1 && (1 : Fin 2) == σ)).toNat = (a i).val
  generalize a i = q
  generalize σ = s
  fin_cases q <;> fin_cases s <;> rfl

def liftOccupation {n : ℕ} (down : Bool) (a : Sector n) : SpinSector n :=
  ⟨spinConfig down a.val, by simp [a.property]⟩

@[simp] theorem toOccupation_lift {n : ℕ} (down : Bool) (a : Sector n) :
    toOccupation (liftOccupation down a) = a :=
  Subtype.ext (occupationOf_spinConfig down a.val)

private abbrev LowOccupation (n : ℕ) := {a : Sector n // active n a.val}
private abbrev LowSpin (n : ℕ) := {a : SpinSector n // active n (occupationOf a.val)}
private abbrev HighSpin (n : ℕ) := {a : SpinSector n // ¬ active n (occupationOf a.val)}
private abbrev Copy (n : ℕ) := {down : Bool // down = true → n = 7}

private def spinCopy {n : ℕ} (a : SpinSector n) : Bool :=
  n == 7 && a.val (3, 1)

private theorem spinConfig_of_active {n : ℕ} (a : SpinSector n)
    (ha : active n (occupationOf a.val)) : liftOccupation (spinCopy a) (toOccupation a) = a := by
  apply Subtype.ext
  funext s
  obtain ⟨i, σ⟩ := s
  have h := ha i
  by_cases hi : i = 3
  · subst i
    by_cases hn : n = 7 <;> fin_cases σ <;>
      cases h₀ : a.val (3, 0) <;> cases h₁ : a.val (3, 1) <;>
      simp_all [liftOccupation, spinConfig, spinCopy, toOccupation, occupationOf]
  · fin_cases σ <;> cases h₀ : a.val (i, 0) <;> cases h₁ : a.val (i, 1) <;>
      simp_all [liftOccupation, spinConfig, spinCopy, toOccupation, occupationOf]

private def lowEquiv (n : ℕ) : Copy n × LowOccupation n ≃ LowSpin n where
  toFun := fun (b, a) => ⟨liftOccupation b.val a.val, by
    change active n (occupationOf (spinConfig b.val a.val.val))
    simpa only [occupationOf_spinConfig] using a.property⟩
  invFun := fun a => (⟨spinCopy a.val, by simp [spinCopy]; exact fun h _ => h⟩,
    ⟨toOccupation a.val, a.property⟩)
  left_inv := by
    rintro ⟨b, a⟩
    apply Prod.ext
    · apply Subtype.ext
      change spinCopy (liftOccupation b.val a.val) = b.val
      by_cases hn : n = 7
      · have hc : a.val.val 3 = 1 := (a.property 3).2 ⟨hn, rfl⟩
        cases h : b.val <;> simp [spinCopy, liftOccupation, spinConfig, hn, hc, h]
      · have hb : b.val = false := by cases h : b.val <;> simp_all [b.property]
        simp [spinCopy, hn, hb]
    · exact Subtype.ext (toOccupation_lift b.val a.val)
  right_inv := fun a => Subtype.ext (spinConfig_of_active a.val a.property)

private def spinSplit (n : ℕ) : (Copy n × LowOccupation n) ⊕ HighSpin n ≃ SpinSector n :=
  ((lowEquiv n).sumCongr (Equiv.refl _)).trans (Equiv.sumCompl _)

private def densitySquare (a : SpinConfig) : ℤ :=
  ∑ i : Fin 7, ((occupationOf a i).val : ℤ) ^ 2

private def orbitPairs := (List.finRange 7).product (List.finRange 7)
private def spinPairs := (List.finRange 2).product (List.finRange 2)

private def filterPairs (p : Fin 7 × Fin 7 → Prop) [DecidablePred p] :
    List {ij // p ij} :=
  orbitPairs.filterMap fun ij => if h : p ij then some ⟨ij, h⟩ else none

private theorem filterPairs_sum {β : Type} [AddCommMonoid β]
    (p : Fin 7 × Fin 7 → Prop) [DecidablePred p] [Fintype {ij // p ij}]
    (f : {ij // p ij} → β) : ((filterPairs p).map f).sum = ∑ ij, f ij := by
  have nodup : orbitPairs.Nodup := by decide +kernel
  have mem (ij : Fin 7 × Fin 7) : ij ∈ orbitPairs := by
    have hu : orbitPairs.toFinset = Finset.univ := by decide +kernel
    rw [← List.mem_toFinset, hu]
    exact Finset.mem_univ ij
  have hn : (filterPairs p).Nodup := by
    unfold filterPairs
    apply List.Nodup.filterMap _ nodup
    intro a b c ha hb
    change (if h : p a then some ⟨a, h⟩ else none) = some c at ha
    change (if h : p b then some ⟨b, h⟩ else none) = some c at hb
    by_cases h₁ : p a <;> by_cases h₂ : p b <;> simp [h₁, h₂] at ha hb
    exact (congrArg Subtype.val ha).trans (congrArg Subtype.val hb).symm
  have hu : (filterPairs p).toFinset = Finset.univ := by
    ext ⟨ij, hi⟩
    simp only [List.mem_toFinset, Finset.mem_univ, iff_true, filterPairs, List.mem_filterMap]
    exact ⟨ij, mem ij, by simp [hi]⟩
  rw [← List.sum_toFinset f hn, hu]

private theorem spinPairs_sum {β : Type} [AddCommMonoid β] (f : Fin 2 × Fin 2 → β) :
    (spinPairs.map f).sum = ∑ ij, f ij := by
  have hn : spinPairs.Nodup := by decide +kernel
  have hu : spinPairs.toFinset = Finset.univ := by decide +kernel
  rw [← List.sum_toFinset f hn, hu]

private def moved {n : ℕ} (a : Sector n) (p : {p // legal a.val p}) : Sector n :=
  ⟨move a.val p.val.1 p.val.2, (neighbors a p).val.property⟩

private def squareRow {n : ℕ} (a : SpinSector n) : List (SpinSector n × ℤ) :=
  (a, densitySquare a.val) ::
    (filterPairs fun ij => ij.1 < ij.2).flatMap fun b =>
      spinPairs.map fun (σ, τ) =>
        let mid := hopPerm b σ a
        (hopPerm b τ mid, hopSign b σ a * hopSign b τ mid)

private def pairedRow {n : ℕ} (down : Bool) (a : Sector n) : List (SpinSector n × ℤ) :=
  (liftOccupation down a, 24 + (n : ℤ) + 2 * (pairNumber a.val : ℤ)) ::
    (filterPairs (legal a.val)).map fun p => (liftOccupation down (moved a p), 2)

private def addTerm {α : Type} [DecidableEq α] (term : α × ℤ) :
    List (α × ℤ) → List (α × ℤ)
  | [] => if term.2 = 0 then [] else [term]
  | entry :: rest =>
    if term.1 = entry.1 then
      if term.2 + entry.2 = 0 then rest else (entry.1, term.2 + entry.2) :: rest
    else entry :: addTerm term rest

private def combineTerms {α : Type} [DecidableEq α] (terms : List (α × ℤ)) :
    List (α × ℤ) :=
  terms.foldr addTerm []

private noncomputable def evaluateRow {α : Type} (x : α → ℝ) (terms : List (α × ℤ)) : ℝ :=
  (terms.map fun (a, v) => (v : ℝ) * x a).sum

private theorem evaluate_addTerm {α : Type} [DecidableEq α] (x : α → ℝ)
    (term : α × ℤ) (terms : List (α × ℤ)) :
    evaluateRow x (addTerm term terms) = (term.2 : ℝ) * x term.1 + evaluateRow x terms := by
  induction terms with
  | nil =>
    by_cases h : term.2 = 0 <;> simp [addTerm, evaluateRow, h]
  | cons e es ih =>
    by_cases he : term.1 = e.1
    · by_cases hz : term.2 + e.2 = 0
      · have hz' : (term.2 : ℝ) + e.2 = 0 := by exact_mod_cast hz
        simp only [addTerm, he, ite_true, hz, evaluateRow, List.map_cons, List.sum_cons]
        rw [← add_assoc, ← add_mul, hz', zero_mul, zero_add]
      · simp only [addTerm, he, ite_true, hz, ite_false, evaluateRow, List.map_cons, List.sum_cons,
          Int.cast_add]
        ring
    · simp only [addTerm, he, ite_false, evaluateRow, List.map_cons, List.sum_cons] at *
      rw [ih]
      ring

private theorem evaluate_combineTerms {α : Type} [DecidableEq α] (x : α → ℝ)
    (terms : List (α × ℤ)) : evaluateRow x (combineTerms terms) = evaluateRow x terms := by
  induction terms with
  | nil => rfl
  | cons e es ih =>
    change evaluateRow x (addTerm e (combineTerms es)) = _
    rw [evaluate_addTerm, ih]
    rfl

private def activeRowTest (n : ℕ) (a : Occupation) : Prop :=
  if hn : electronCount a = n then
    if active n a then ∀ b : Bool,
      (combineTerms (squareRow (liftOccupation b ⟨a, hn⟩))).Perm
        (combineTerms (pairedRow b ⟨a, hn⟩))
    else True
  else True

private instance (n : ℕ) (a : Occupation) : Decidable (activeRowTest n a) := by
  unfold activeRowTest
  infer_instance

set_option maxHeartbeats 0 in
set_option maxRecDepth 15000 in
private theorem activeRowChecks (k : Fin 3) (chunk : Fin 27) :
    ∀ offset : Fin 81, activeRowTest (6 + k.val) (decode (81 * chunk.val + offset.val)) := by
  fin_cases k <;> fin_cases chunk <;> decide +kernel

private theorem activeRows (k : Fin 3) (a : LowOccupation (6 + k.val)) (b : Bool) :
    (combineTerms (squareRow (liftOccupation b a.val))).Perm
      (combineTerms (pairedRow b a.val)) := by
  have h : ∀ c : Fin 2187, activeRowTest (6 + k.val) (decode c.val) := by
    intro c
    have hq : c.val / 81 < 27 := by omega
    have hr : c.val % 81 < 81 := by omega
    have hc : 81 * (c.val / 81) + c.val % 81 = c.val := by omega
    simpa only [hc] using activeRowChecks k ⟨c.val / 81, hq⟩ ⟨c.val % 81, hr⟩
  have check := for_all_occupations h a.val.val
  simp only [activeRowTest, dite_eq_left a.val.property, ite_eq_left a.property] at check
  exact check b

noncomputable def squareAction {n : ℕ} (x : SpinSector n → ℝ) (a : SpinSector n) : ℝ :=
  ∑ m : Mode, vertex m (vertex m x) a

private theorem sum_flatMap_map {α β γ : Type} [AddCommMonoid γ] (l : List α)
    (f : α → List β) (g : β → γ) :
    ((l.flatMap f).map g).sum = (l.map fun a => ((f a).map g).sum).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, List.sum_append, ih]

private theorem squareAction_row {n : ℕ} (x : SpinSector n → ℝ) (a : SpinSector n) :
    squareAction x a = evaluateRow x (squareRow a) := by
  unfold evaluateRow squareRow
  rw [List.map_cons, List.sum_cons, sum_flatMap_map, filterPairs_sum]
  simp only [List.map_map, Function.comp_def, spinPairs_sum, Fintype.sum_prod_type,
    squareAction, Fintype.sum_sum_type, vertex, Finset.mul_sum, mul_assoc, Int.cast_mul]
  rw [add_comm]
  congr 1
  unfold densitySquare
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem low_squareAction (k : Fin 3) (x : SpinSector (6 + k.val) → ℝ)
    (b : Copy (6 + k.val)) (a : LowOccupation (6 + k.val)) :
    squareAction x (liftOccupation b.val a.val) =
      (24 + (6 + k.val : ℕ) + 2 * pairNumber a.val.val : ℝ) * x (liftOccupation b.val a.val) +
        2 * ∑ p : {p // legal a.val.val p}, x (liftOccupation b.val (neighbors a.val p).val) := by
  rw [squareAction_row]
  have he := ((activeRows k a b.val).map (fun (j, v) => (v : ℝ) * x j)).sum_eq
  change evaluateRow x (combineTerms (squareRow _)) = evaluateRow x (combineTerms (pairedRow _ _)) at he
  simp only [evaluate_combineTerms] at he
  rw [he]
  simp only [evaluateRow, pairedRow, List.map_cons, List.sum_cons, List.map_map,
    Function.comp_def, filterPairs_sum, Int.cast_add, Int.cast_mul, Int.cast_ofNat,
    Int.cast_natCast, Finset.mul_sum]
  rfl

private theorem neighbor_active {n : ℕ} (a : LowOccupation n) (p : {p // legal a.val.val p}) :
    active n (neighbors a.val p).val.val := by
  have hn : p.val.1 ≠ p.val.2 := by
    intro he
    have h := p.property.1
    rw [he, p.property.2] at h
    contradiction
  change active n (move a.val.val p.val.1 p.val.2)
  intro i
  by_cases h₁ : i = p.val.1
  · subst i
    simpa [move, p.property.1] using a.property p.val.1
  by_cases h₂ : i = p.val.2
  · subst i
    simpa [move, hn.symm, p.property.2] using a.property p.val.2
  · simpa [move, h₁, h₂] using a.property i

private theorem electronic_row {n : ℕ} (r s : ℚ) (a : Sector n) (x : Sector n → ℝ) :
    (∑ j, (ratH r s n a j : ℝ) * x j) =
      (diagonal r s a.val : ℝ) * x a -
        (coupling : ℝ) * ∑ p : {p // legal a.val p}, x (neighbors a p).val := by
  have h (j : Sector n) :
      (ratH r s n a j : ℝ) * x j =
      (if a = j then (diagonal r s a.val : ℝ) * x a else 0) -
        (if Hop a.val j.val then (coupling : ℝ) * x j else 0) := by
    rcases eq_or_ne a j with rfl | hne
    · have hn : ¬ Hop a.val a.val := by
        rintro ⟨i, j, hi, _, hm⟩
        have hz := congrFun hm i
        simp [move, hi] at hz
      simp [ratH, hn]
    · by_cases hh : Hop a.val j.val <;> simp [ratH, hne, hh, neg_mul]
  simp_rw [h]
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ a), Finset.mul_sum]
  rw [← Finset.sum_filter, Finset.sum_subtype (p := fun j : Sector n => Hop a.val j.val)
    _ (by simp)]
  exact congrArg ((diagonal r s a.val : ℝ) * x a - ·)
    (Equiv.sum_comp (neighbors a) (fun j => (coupling : ℝ) * x j.val)).symm

private noncomputable def comparisonAction (r s : ℚ) {n : ℕ}
    (x : SpinSector n → ℝ) (a : SpinSector n) : ℝ :=
  (kineticDiagonal r s a : ℝ) * x a - frequency * mixing ^ 2 * squareAction x a

private theorem comparison_form (r s : ℚ) {n : ℕ} (x : SpinSector n → ℝ) :
    effective (kineticForm r s) vertex frequency mixing x = inner x (comparisonAction r s x) := by
  have hs (m : Mode) : inner x (vertex m (vertex m x)) = normSq (vertex m x) := by
    rw [vertex_symmetric, inner_self]
  have hsum :
      (∑ a, x a * (frequency * mixing ^ 2 * squareAction x a)) =
        frequency * mixing ^ 2 * ∑ m, inner x (vertex m (vertex m x)) := by
    simp only [squareAction, inner, Finset.mul_sum]
    rw [Finset.sum_comm (f := fun m a => frequency * mixing ^ 2 *
      (x a * vertex m (vertex m x) a))]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro m _
    ring
  simp only [effective, kineticForm, vertexNorm, comparisonAction, squareAction, inner,
    mul_sub, Finset.sum_sub_distrib]
  change _ - _ = _ - ∑ a, x a * (frequency * mixing ^ 2 * squareAction x a)
  rw [hsum]
  simp only [hs]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  ring

private theorem comparison_symm (r s : ℚ) {n : ℕ} (x y : SpinSector n → ℝ) :
    inner x (comparisonAction r s y) = inner y (comparisonAction r s x) := by
  have hs (m : Mode) : inner x (vertex m (vertex m y)) = inner y (vertex m (vertex m x)) := by
    rw [vertex_symmetric, vertex_symmetric]
    simp only [inner, mul_comm]
  have hsum (u v : SpinSector n → ℝ) :
      (∑ a, u a * (frequency * mixing ^ 2 * squareAction v a)) =
      frequency * mixing ^ 2 * ∑ m, inner u (vertex m (vertex m v)) := by
    simp only [squareAction, inner, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro m _
    ring
  unfold comparisonAction
  simp only [inner, mul_sub, Finset.sum_sub_distrib]
  rw [hsum, hsum]
  simp_rw [hs]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  ring

private theorem comparison_add (r s : ℚ) {n : ℕ} (x y : SpinSector n → ℝ) :
    comparisonAction r s (x + y) = comparisonAction r s x + comparisonAction r s y := by
  have hv (m : Mode) (u v : SpinSector n → ℝ) : vertex m (u + v) = vertex m u + vertex m v := by
    funext a
    cases m <;> simp [vertex, mul_add, Finset.sum_add_distrib]
  funext a
  simp [comparisonAction, squareAction, hv, mul_add, Finset.sum_add_distrib]
  ring

private noncomputable def restrictedVector {n : ℕ} (b : Copy n) (x : SpinSector n → ℝ)
    (a : Sector n) : ℝ :=
  if active n a.val then x (liftOccupation b.val a) else 0

private theorem low_comparisonAction (r s : ℚ) (k : Fin 3)
    (x : SpinSector (6 + k.val) → ℝ) (b : Copy (6 + k.val)) (a : LowOccupation (6 + k.val)) :
    comparisonAction r s x (liftOccupation b.val a.val) =
      (∑ j, (ratH r s (6 + k.val) a.val j : ℝ) * restrictedVector b x j) +
        electronicShift k * x (liftOccupation b.val a.val) := by
  rw [comparisonAction, low_squareAction, electronic_row]
  simp only [restrictedVector, ite_eq_left a.property, ite_eq_left (neighbor_active a _)]
  have hkin : kineticDiagonal r s (liftOccupation b.val a.val) =
      diagonal r s a.val + coupling * pairNumber a.val.val := by
    simp [kineticDiagonal, liftOccupation, diagonal]
  rw [hkin]
  push_cast
  unfold electronicShift
  norm_num [frequency, mixing, coupling]
  ring

private def lowPart {n : ℕ} (x : SpinSector n → ℝ) (a : SpinSector n) : ℝ :=
  if active n (occupationOf a.val) then x a else 0

private def highPart {n : ℕ} (x : SpinSector n → ℝ) (a : SpinSector n) : ℝ :=
  if active n (occupationOf a.val) then 0 else x a

private theorem lowPart_add_highPart {n : ℕ} (x : SpinSector n → ℝ) :
    lowPart x + highPart x = x := by
  funext a
  by_cases h : active n (occupationOf a.val) <;> simp [lowPart, highPart, h]

@[simp] private theorem spinSplit_low {n : ℕ} (b : Copy n) (a : LowOccupation n) :
    spinSplit n (Sum.inl (b, a)) = liftOccupation b.val a.val := rfl

@[simp] private theorem spinSplit_high {n : ℕ} (a : HighSpin n) :
    spinSplit n (Sum.inr a) = a.val := rfl

private theorem lowPart_lift {n : ℕ} (x : SpinSector n → ℝ) (b : Copy n) (a : LowOccupation n) :
    lowPart x (liftOccupation b.val a.val) = x (liftOccupation b.val a.val) := by
  simp [lowPart, liftOccupation, a.property]

private theorem highPart_lift {n : ℕ} (x : SpinSector n → ℝ) (b : Copy n) (a : LowOccupation n) :
    highPart x (liftOccupation b.val a.val) = 0 := by
  simp [highPart, liftOccupation, a.property]

private theorem restricted_lowPart {n : ℕ} (b : Copy n) (x : SpinSector n → ℝ) :
    restrictedVector b (lowPart x) = restrictedVector b x := by
  funext a
  by_cases h : active n a.val <;> simp [restrictedVector, lowPart, liftOccupation, h]

private theorem restricted_highPart {n : ℕ} (b : Copy n) (x : SpinSector n → ℝ) :
    restrictedVector b (highPart x) = 0 := by
  funext a
  by_cases h : active n a.val <;> simp [restrictedVector, highPart, liftOccupation, h]

private theorem zero_extended_sum {n : ℕ} (f : Sector n → ℝ) :
    (∑ a : LowOccupation n, f a.val) = ∑ a : Sector n, if active n a.val then f a else 0 := by
  rw [← Finset.sum_filter, Finset.sum_subtype (p := fun a : Sector n => active n a.val)
    _ (by simp)]

private theorem comparison_split (r s : ℚ) (k : Fin 3) (x : SpinSector (6 + k.val) → ℝ) :
    effective (kineticForm r s) vertex frequency mixing x =
      (∑ b : Copy (6 + k.val), (form (ratH r s (6 + k.val)) (restrictedVector b x) +
        electronicShift k * normSq (restrictedVector b x))) +
      effective (kineticForm r s) vertex frequency mixing (highPart x) := by
  let lo := lowPart x
  let hi := highPart x
  have cross : inner lo (comparisonAction r s hi) = 0 := by
    unfold inner
    rw [← Equiv.sum_comp (spinSplit (6 + k.val))]
    simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, spinSplit_low, spinSplit_high,
      low_comparisonAction, lo, hi, restricted_highPart, highPart_lift,
      show ∀ a : HighSpin (6 + k.val), lowPart x a.val = 0 from
        fun a => ite_eq_right a.property,
      Pi.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
  have lowForm : inner lo (comparisonAction r s lo) =
      ∑ b : Copy (6 + k.val), (form (ratH r s (6 + k.val)) (restrictedVector b x) +
        electronicShift k * normSq (restrictedVector b x)) := by
    unfold inner
    rw [← Equiv.sum_comp (spinSplit (6 + k.val))]
    simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, spinSplit_low, spinSplit_high,
      low_comparisonAction, lo, restricted_lowPart, lowPart_lift,
      show ∀ a : HighSpin (6 + k.val), lowPart x a.val = 0 from
        fun a => ite_eq_right a.property, zero_mul, Finset.sum_const_zero, add_zero]
    apply Finset.sum_congr rfl
    intro b _
    rw [zero_extended_sum (fun a =>
      x (liftOccupation b.val a) *
        ((∑ j, (ratH r s (6 + k.val) a j : ℝ) * restrictedVector b x j) +
          electronicShift k * x (liftOccupation b.val a)))]
    simp only [form, normSq, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : active (6 + k.val) a.val <;>
      simp [ha, restrictedVector, Finset.mul_sum, mul_add, pow_two, mul_left_comm, mul_comm]
    apply Finset.sum_congr rfl
    intro j _
    split <;> simp [mul_assoc]
  rw [comparison_form, comparison_form, ← lowForm]
  conv_lhs => rw [← lowPart_add_highPart x]
  change inner (lo + hi) (comparisonAction r s (lo + hi)) =
    inner lo (comparisonAction r s lo) + inner hi (comparisonAction r s hi)
  rw [comparison_add]
  have addInner (a b c d : SpinSector (6 + k.val) → ℝ) :
      inner (a + b) (c + d) = inner a c + inner a d + inner b c + inner b d := by
    simp [inner, add_mul, mul_add, Finset.sum_add_distrib]
    ring
  rw [addInner, comparison_symm r s hi lo, cross]
  ring

private theorem norm_split (k : Fin 3) (x : SpinSector (6 + k.val) → ℝ) :
    normSq x = (∑ b : Copy (6 + k.val), normSq (restrictedVector b x)) +
      normSq (highPart x) := by
  unfold normSq
  rw [← Equiv.sum_comp (spinSplit (6 + k.val)), ← Equiv.sum_comp (spinSplit (6 + k.val))
    (fun a => highPart x a ^ 2)]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, spinSplit_low, spinSplit_high,
    highPart_lift, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, zero_add,
    show ∀ a : HighSpin (6 + k.val), highPart x a.val = x a.val from
      fun a => ite_eq_right a.property]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  rw [zero_extended_sum (fun a => x (liftOccupation b.val a) ^ 2)]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : active (6 + k.val) a.val <;> simp [restrictedVector, h]

private def shiftedHi (r s : Bool) (k : Fin 3) : ℚ :=
  (FullSolve.witness r s k).hi - coupling * (12 + (6 + (k.val : ℚ)) / 2)

theorem shiftedHi_eq (r s : Bool) (k : Fin 3) :
    (shiftedHi r s k : ℝ) = (FullSolve.witness r s k).hi + electronicShift k := by
  simp [shiftedHi, electronicShift, sub_eq_add_neg]

theorem shifted_upper_budget (r s : Bool) (k : Fin 3) :
    let u : ℝ := (FullSolve.witness r s k).hi + electronicShift k;
    -81 ≤ u ∧ u ≤ 80 ∧ u ≤ Prediction.energy r s k + electronicShift k + 1 / 10^13 := by
  dsimp only
  have limits : (-81 : ℚ) ≤ shiftedHi r s k ∧ shiftedHi r s k ≤ 80 ∧
      (FullSolve.witness r s k).hi - (FullSolve.witness r s k).lo ≤ 1 / 10^13 := by
    cases r <;> cases s <;> fin_cases k <;> decide +kernel
  have hlo := (FullSolve.sector_bounds r s k).1
  have gap : (((FullSolve.witness r s k).hi : ℚ) : ℝ) -
      (FullSolve.witness r s k).lo ≤ 1 / 10^13 := by
    have h := (Rat.cast_le (K := ℝ)).mpr limits.2.2
    push_cast at h
    exact h
  rw [← shiftedHi_eq]
  refine ⟨by exact_mod_cast limits.1, by exact_mod_cast limits.2.1, ?_⟩
  rw [shiftedHi_eq]
  linarith

private def kineticTest (r s : Bool) (k : Fin 3) (a : Occupation) : Prop :=
  let energy := ∑ i : Fin 7, ((a i).val : ℚ) *
    rationalLevels (Prediction.innerRadius r) (Prediction.outerRadius s) i
  energy ≤ 80 ∧
    (electronCount a = 6 + k.val → ¬ active (6 + k.val) a → shiftedHi r s k + 112 / 200 ≤ energy)

private instance (r s : Bool) (k : Fin 3) (a : Occupation) : Decidable (kineticTest r s k a) := by
  unfold kineticTest
  infer_instance

set_option maxHeartbeats 0 in
set_option maxRecDepth 15000 in
private theorem kineticChecks (r s : Bool) (k : Fin 3) (chunk : Fin 27) :
    ∀ offset : Fin 81, kineticTest r s k (decode (81 * chunk.val + offset.val)) := by
  cases r <;> cases s <;> fin_cases k <;> fin_cases chunk <;> decide +kernel

private theorem kinetic_test (r s : Bool) (k : Fin 3) (a : Occupation) : kineticTest r s k a := by
  apply for_all_occupations _ a
  intro c
  have hq : c.val / 81 < 27 := by omega
  have hr : c.val % 81 < 81 := by omega
  have hc : 81 * (c.val / 81) + c.val % 81 = c.val := by omega
  simpa only [hc] using kineticChecks r s k ⟨c.val / 81, hq⟩ ⟨c.val % 81, hr⟩

theorem kinetic_le (r s : Bool) (k : Fin 3) (x : SpinSector (6 + k.val) → ℝ) :
    kineticForm (Prediction.innerRadius r) (Prediction.outerRadius s) x ≤ 80 * normSq x := by
  unfold kineticForm normSq
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact_mod_cast (kinetic_test r s k (occupationOf a.val)).1

private theorem high_lower (r s : Bool) (k : Fin 3) (x : SpinSector (6 + k.val) → ℝ) :
    (shiftedHi r s k : ℝ) * normSq (highPart x) ≤
      effective (kineticForm (Prediction.innerRadius r) (Prediction.outerRadius s))
        vertex frequency mixing (highPart x) := by
  have hkin : ((shiftedHi r s k : ℝ) + 112 / 200) * normSq (highPart x) ≤
      kineticForm (Prediction.innerRadius r) (Prediction.outerRadius s) (highPart x) := by
    unfold normSq kineticForm
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a _
    by_cases ha : active (6 + k.val) (occupationOf a.val)
    · simp [highPart, ha]
    · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      have h : shiftedHi r s k + 112 / 200 ≤
          kineticDiagonal (Prediction.innerRadius r) (Prediction.outerRadius s) a :=
        (kinetic_test r s k (occupationOf a.val)).2 a.property ha
      have hc := (Rat.cast_le (K := ℝ)).mpr h
      push_cast at hc
      exact hc
  have hv := vertexNorm_le (highPart x)
  unfold effective
  norm_num [frequency, mixing] at *
  linarith

private theorem reduced_lower (r s : ℚ) {n : ℕ} (x : Sector n → ℝ) :
    ground (ratH r s n) * normSq x ≤ form (ratH r s n) x := by
  let H := ratH r s n
  let lo := - ∑ a, |action H (fun _ => 1) a|
  have bound (y : Sector n → ℝ) : (lo : ℝ) * normSq y ≤ form H y := by
    apply weighted_lower H (fun _ => 1) lo
    · intro i j
      apply Rat.cast_injective (α := ℝ)
      unfold H
      simp only [ratH_cast]
      exact hamiltonian_symmetric n 1 r s coupling i j
    · intro i j h
      by_cases hh : Hop i.val j.val <;> norm_num [H, ratH, h, hh, coupling]
    · intro i
      norm_num
    · intro i
      simp only [mul_one]
      have hi : |action H (fun _ => 1) i| ≤ ∑ a, |action H (fun _ => 1) a| :=
        Finset.single_le_sum (f := fun a => |action H (fun _ => 1) a|)
          (fun a _ => abs_nonneg _) (Finset.mem_univ i)
      linarith [neg_abs_le (action H (fun _ => 1) i)]
  have bdd : BddBelow (energies H) := by
    refine ⟨lo, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact (le_div_iff₀ hy).2 (bound y)
  by_cases hx : 0 < normSq x
  · apply (le_div_iff₀ hx).1
    exact csInf_le bdd ⟨x, hx, rfl⟩
  · have zero : x = 0 := by
      have hz : normSq x = 0 := le_antisymm (le_of_not_gt hx) (normSq_nonneg x)
      funext i
      have hi : x i ^ 2 ≤ normSq x := Finset.single_le_sum
        (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
      simp only [Pi.zero_apply]
      nlinarith
    simp [zero, normSq, form]

theorem electronic_lower (r s : Bool) (k : Fin 3) (x : SpinSector (6 + k.val) → ℝ) :
    (Prediction.energy r s k + electronicShift k) * normSq x ≤
      effective (kineticForm (Prediction.innerRadius r) (Prediction.outerRadius s))
        vertex frequency mixing x := by
  rw [comparison_split, norm_split]
  have hh : Prediction.energy r s k + electronicShift k ≤ shiftedHi r s k := by
    rw [shiftedHi_eq]
    linarith [(FullSolve.sector_bounds r s k).2]
  have hhigh := (mul_le_mul_of_nonneg_right hh (normSq_nonneg (highPart x))).trans (high_lower r s k x)
  rw [mul_add, Finset.mul_sum]
  apply add_le_add _ hhigh
  apply Finset.sum_le_sum
  intro b _
  have hl := reduced_lower (Prediction.innerRadius r) (Prediction.outerRadius s) (restrictedVector b x)
  change Prediction.energy r s k * normSq (restrictedVector b x) ≤ _ at hl
  linarith

private theorem trial_row (r s : Bool) (k : Fin 3) :
    let w := FullSolve.witness r s k
    let H := ratH (Prediction.innerRadius r) (Prediction.outerRadius s) (6 + k.val)
    let x : Sector (6 + k.val) → ℚ := fun a => trialVector (6 + k.val) w a.val
    rayleighNumerator H x ≤ w.hi * rationalNormSq x := by
  dsimp only
  let w := FullSolve.witness r s k
  unfold rayleighNumerator rationalNormSq
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : active (6 + k.val) a.val
  · have hr := rows_from_chunks _ _ _ _ (FullSolve.witness_rows r s k) a.val
    simp only [rowTest, a.property, ite_true, ite_eq_left ha] at hr
    rw [sparseAction_eq]
    have hact : sparseAction (Prediction.innerRadius r) (Prediction.outerRadius s)
        (trialVector (6 + k.val) w) a.val =
        sparseAction (Prediction.innerRadius r) (Prediction.outerRadius s) (amplitude w) a.val := by
      unfold sparseAction
      simp only [trialVector, ite_eq_left ha]
      congr 2
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : legal a.val p
      · have h := neighbor_active ⟨a, ha⟩ ⟨p, hp⟩
        change active _ (move a.val p.1 p.2) at h
        simp [hp, h]
      · simp [hp]
    rw [hact]
    simp only [trialVector, ite_eq_left ha]
    nlinarith only [mul_le_mul_of_nonneg_left hr.2.2 hr.1.le]
  · simp [trialVector, ha]

private theorem trial_pos (r s : Bool) (k : Fin 3) :
    0 < rationalNormSq (fun a : Sector (6 + k.val) =>
      trialVector (6 + k.val) (FullSolve.witness r s k) a.val) := by
  let a := decode (26 + 27 * k.val)
  have hn : electronCount a = 6 + k.val := by fin_cases k <;> decide +kernel
  have ha : active (6 + k.val) a := by fin_cases k <;> decide +kernel
  have hr := rows_from_chunks _ _ _ _ (FullSolve.witness_rows r s k) a
  simp only [rowTest, hn, ite_true, ite_eq_left ha] at hr
  unfold rationalNormSq
  apply lt_of_lt_of_le _ (Finset.single_le_sum (fun i _ => sq_nonneg
    (trialVector _ (FullSolve.witness r s k) i.val)) (Finset.mem_univ ⟨a, hn⟩))
  simp [trialVector, ha, sq_pos_of_pos hr.1]

theorem electronic_trial (r s : Bool) (k : Fin 3) :
    ∃ x : SpinSector (6 + k.val) → ℝ, normSq x = 1 ∧
      effective (kineticForm (Prediction.innerRadius r) (Prediction.outerRadius s))
        vertex frequency mixing x ≤ (FullSolve.witness r s k).hi + electronicShift k := by
  classical
  let n := 6 + k.val
  let w := FullSolve.witness r s k
  let t : Sector n → ℚ := fun a => trialVector n w a.val
  let v : Sector n → ℝ := fun a => (t a : ℝ) / Real.sqrt (rationalNormSq t : ℝ)
  let b₀ : Copy n := ⟨false, by simp⟩
  let x : SpinSector n → ℝ := fun i =>
    Sum.elim (fun (b, a) => if b = b₀ then v a.val else 0) (fun _ => 0) ((spinSplit n).symm i)
  have vzero (a : Sector n) (ha : ¬active n a.val) : v a = 0 := by
    simp [v, t, trialVector, ha]
  have hxhigh : highPart x = 0 := by
    funext i
    by_cases hi : active n (occupationOf i.val)
    · simp [highPart, hi]
    · have he : spinSplit n (.inr ⟨i, hi⟩) = i := spinSplit_high ⟨i, hi⟩
      rw [show highPart x i = x i from ite_eq_right hi]
      change Sum.elim _ _ ((spinSplit n).symm i) = 0
      rw [← he, Equiv.symm_apply_apply]
      rfl
  have hxlow (b : Copy n) : restrictedVector b x = if b = b₀ then v else 0 := by
    funext a
    by_cases ha : active n a.val
    · have he : spinSplit n (.inl (b, ⟨a, ha⟩)) = liftOccupation b.val a := spinSplit_low b ⟨a, ha⟩
      rw [show restrictedVector b x a = x (liftOccupation b.val a) from ite_eq_left ha]
      change Sum.elim _ _ ((spinSplit n).symm (liftOccupation b.val a)) = _
      rw [← he, Equiv.symm_apply_apply]
      by_cases hb : b = b₀ <;> simp [hb]
    · by_cases hb : b = b₀ <;> simp [restrictedVector, ha, hb, vzero a ha]
  have hpos : 0 < (rationalNormSq t : ℝ) := by exact_mod_cast trial_pos r s k
  have hs : Real.sqrt (rationalNormSq t : ℝ) ^ 2 = (rationalNormSq t : ℝ) :=
    Real.sq_sqrt hpos.le
  have hvnorm : normSq v = 1 := by
    simp only [normSq, v, div_pow, ← Finset.sum_div, hs]
    rw [← normSq, normSq_cast, div_self hpos.ne']
  refine ⟨x, ?_, ?_⟩
  · rw [norm_split, hxhigh]
    simp [hxlow, apply_ite normSq, normSq_zero, hvnorm]
  · rw [comparison_split, hxhigh]
    have zero (m : Mode) : vertex (n := n) m 0 = 0 := by
      funext a
      cases m <;> simp [vertex]
    have form_zero : form (ratH (Prediction.innerRadius r) (Prediction.outerRadius s) n) 0 = 0 := by
      simp [form]
    have effective_zero : effective (kineticForm (Prediction.innerRadius r) (Prediction.outerRadius s))
        (vertex (n := n)) frequency mixing 0 = 0 := by
      simp only [effective, kineticForm, vertexNorm, zero, normSq_zero, Pi.zero_apply, zero_pow
        (by decide : 2 ≠ 0), mul_zero, Finset.sum_const_zero, sub_zero]
    let H := ratH (Prediction.innerRadius r) (Prediction.outerRadius s) n
    have hsum (b : Copy n) : form H (restrictedVector b x) +
        electronicShift k * normSq (restrictedVector b x) =
        if b = b₀ then form H v + electronicShift k else 0 := by
      rw [hxlow b]
      by_cases hb : b = b₀
      · simp [hb, hvnorm]
      · simp only [ite_eq_right hb, show form H 0 = 0 from form_zero,
          normSq_zero, mul_zero, add_zero]
    change (∑ b : Copy n, (form H (restrictedVector b x) +
      electronicShift k * normSq (restrictedVector b x))) +
      effective _ _ _ _ _ ≤ _
    simp only [hsum, effective_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, add_zero]
    have hform : form (ratH (Prediction.innerRadius r) (Prediction.outerRadius s) n) v ≤
        ((w.hi : ℚ) : ℝ) := by
      have term (a b : Sector n) :
          v a * v b = ((t a : ℝ) * t b) / (rationalNormSq t : ℝ) := by
        rw [show v a * v b = ((t a : ℝ) / Real.sqrt (rationalNormSq t : ℝ)) *
          ((t b : ℝ) / Real.sqrt (rationalNormSq t : ℝ)) from rfl, div_mul_div_comm,
          ← pow_two, hs]
      simp only [form, term, ← mul_div_assoc, ← Finset.sum_div]
      apply (div_le_iff₀ hpos).2
      have h : ((rayleighNumerator (ratH (Prediction.innerRadius r) (Prediction.outerRadius s) n) t : ℚ) : ℝ) ≤
          (w.hi : ℝ) * (rationalNormSq t : ℝ) := by exact_mod_cast trial_row r s k
      rw [← form_cast] at h
      exact h
    change form H v + electronicShift k ≤ (w.hi : ℝ) + electronicShift k
    linarith

end Grain.Phonon
