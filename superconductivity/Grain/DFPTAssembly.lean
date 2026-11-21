import Grain.HarmonicBand
import Grain.SparseForm

/-! Executable sparse columns for the exported harmonic Hamiltonian. -/

namespace Grain.HarmonicBand

open Sparse
open scoped BigOperators

variable {n c m : ℕ}

private theorem slot_lt (p : Spin n) : slot p < 2*n := by
  have := p.1.isLt
  have := p.2.isLt
  unfold slot
  omega

private theorem flip_lt (p : Spin n) (a : State n) :
    a.val ^^^ 2 ^ slot p < 2 ^ (2*n) :=
  Nat.xor_lt_two_pow a.isLt (Nat.pow_lt_pow_right (by decide) (slot_lt p))

private theorem flip_bit (p : Spin n) (a : State n) (j : ℕ) :
    (a.val ^^^ 2 ^ slot p).testBit j =
      (a.val.testBit j ^^ decide (slot p = j)) := by
  rw [Nat.testBit_xor, Nat.testBit_two_pow]

private theorem phase_flip (p : Spin n) (a : State n) :
    (List.range (slot p)).countP (a.val ^^^ 2 ^ slot p).testBit =
      (List.range (slot p)).countP a.val.testBit := by
  apply List.countP_congr
  intro j hj
  rw [flip_bit]
  simp [show slot p ≠ j by have := List.mem_range.mp hj; omega]

private theorem step_reverse (create : Bool) (p : Spin n) (a b : State n) (s : ℤ) :
    step create p a = some (b, s) → step (!create) p b = some (a, s) := by
  unfold step
  split
  · simp
  · rename_i h
    intro he
    have hb : b = Fin.ofNat _ (a.val ^^^ 2 ^ slot p) := by simpa using (congrArg (Option.map Prod.fst) he).symm
    subst b
    have hv : (Fin.ofNat (2 ^ (2*n)) (a.val ^^^ 2 ^ slot p)).val =
        a.val ^^^ 2 ^ slot p := Nat.mod_eq_of_lt (flip_lt p a)
    have ha : Fin.ofNat (2 ^ (2*n)) ((a.val ^^^ 2 ^ slot p) ^^^ 2 ^ slot p) = a := by
      apply Fin.ext
      rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
      exact Nat.mod_eq_of_lt a.isLt
    rw [show occupied (Fin.ofNat _ (a.val ^^^ 2 ^ slot p)) p = !occupied a p by
      unfold occupied
      rw [hv, flip_bit]
      simp]
    cases create <;> cases ho : occupied a p <;>
      simp_all [phase_flip]

private def hopColumn (p q : Spin n) (j : State n) : Vector (State n) :=
  match step false q j with
  | none => []
  | some (b, t) => match step true p b with
    | none => []
    | some (i, s) => [(i, (s : ℚ) * t)]

private theorem hop_entry (p q : Spin n) (i j : State n) :
    entry (hopColumn p q j) i = annihilationOverlap p q i j := by
  unfold hopColumn annihilationOverlap
  cases hq : step false q j with
  | none => cases step false p i <;> rfl
  | some qout =>
    obtain ⟨b,t⟩ := qout
    cases hp : step false p i with
    | none =>
      cases hc : step true p b with
      | none => simp [hc]
      | some pout =>
        obtain ⟨a,s⟩ := pout
        have hr := step_reverse true p b a s hc
        change step false p a = some (b,s) at hr
        have hne : i ≠ a := by
          intro he; subst i; rw [hp] at hr; contradiction
        simp [hc, hne]
    | some pout =>
      obtain ⟨a,s⟩ := pout
      by_cases hsame : a = b
      · subst a
        have hr := step_reverse false p i b s hp
        change step true p b = some (i,s) at hr
        simp [hr]
      · cases hc : step true p b with
        | none => simp [hc, hsame]
        | some cout =>
          obtain ⟨k,u⟩ := cout
          have hr := step_reverse true p b k u hc
          change step false p k = some (b,u) at hr
          have hne : i ≠ k := by
            intro he; subst k
            rw [hp] at hr
            exact hsame (Prod.mk.inj (Option.some.inj hr)).1
          simp [hc, hsame, hne]

private theorem entry_flatMap {ι α : Type} [DecidableEq ι] (l : List α)
    (f : α → Vector ι) (i : ι) :
    entry (l.flatMap f) i = (l.map fun a => entry (f a) i).sum := by
  induction l <;> simp_all

abbrev OrbitalEntry (n : ℕ) := Orbital n × Orbital n × ℚ

def modeEntries (d : Input n c m) (k : Fin m) : List (OrbitalEntry n) :=
  (List.finRange n).flatMap fun p => (List.finRange n).filterMap fun q =>
    let a := modeEntry d k p q
    if a = 0 then none else some (p, q, a)

def modeColumns (e : List (OrbitalEntry n)) (j : State n) : Vector (State n) :=
  e.flatMap fun (p, q, a) => (List.finRange 2).flatMap fun s =>
    scale a (hopColumn (p,s) (q,s) j)

def vertexColumns (d : Input n c m) : Fin m → State n → Vector (State n) :=
  fun k => modeColumns (modeEntries d k)

private theorem sum_filterMap {α β : Type} (f : α → Option β) (g : β → ℚ) (xs : List α) :
    ((xs.filterMap f).map g).sum = (xs.map fun a => ((f a).map g).getD 0).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih => cases h : f a <;> simp [h, ih]

@[simp] theorem vertexColumns_entry (d : Input n c m) (k : Fin m) (i j : State n) :
    entry (vertexColumns d k j) i = electronPhonon d k i j := by
  unfold vertexColumns modeColumns modeEntries electronPhonon oneBody
  rw [List.flatMap_assoc]
  simp only [entry_flatMap]
  conv_rhs => rw [Fin.sum_univ_def]
  congr 1
  apply List.map_congr_left
  intro p _
  rw [sum_filterMap, Fin.sum_univ_def]
  congr 1
  apply List.map_congr_left
  intro q _
  split <;> rename_i h
  · simp [h]
  · simp [hop_entry, Fin.sum_univ_def]

def kineticValue (d : Input n c m) (j : State n) : ℚ :=
  ((List.finRange n).map fun p =>
    ((List.finRange 2).map fun s => if occupied j (p,s) then d.levels p else 0).sum).sum

def interactionColumn (d : Input n c m) (j : State n) : Vector (State n) :=
  (j, ((d.density.filter fun (t : Density n) => occupied j t.first && occupied j t.second).map
    Density.strength).sum) :: scatteringColumn d j

def electronicColumn (d : Input n c m) (j : State n) : Vector (State n) :=
  (j, kineticValue d j) :: interactionColumn d j

@[simp] theorem electronicColumn_entry (d : Input n c m) (i j : State n) :
    entry (electronicColumn d j) i = electronic d i j := by
  have h (v : Vector (State n)) : entry v i = columnEntry v i := by
    induction v with
    | nil => rfl
    | cons t v ih =>
      obtain ⟨k,a⟩ := t
      by_cases he : i = k
      · subst k; simp [columnEntry] at ih ⊢; exact ih
      · simpa [columnEntry, he, Ne.symm he] using ih
  unfold electronicColumn interactionColumn electronic kinetic screened kineticValue
  rw [entry_cons, entry_cons, h]
  by_cases he : i = j <;>
    simp only [he, ite_true, ite_false, zero_add, Fin.sum_univ_def]

def inducedColumns (d : Input n c m) (modes : Fin m → List (OrbitalEntry n))
    (j : State n) : Vector (State n) :=
  (List.finRange m).flatMap fun k =>
    let A := modeColumns (modes k)
    scale (-1 / (2 * d.force k)) (Sparse.apply A (A j))

def perturbationColumn (d : Input n c m) (modes : Fin m → List (OrbitalEntry n))
    (j : State n) : Vector (State n) :=
  interactionColumn d j ++ inducedColumns d modes j

def instantaneousColumnWith (d : Input n c m) (modes : Fin m → List (OrbitalEntry n))
    (j : State n) : Vector (State n) :=
  (j, kineticValue d j) :: compact (perturbationColumn d modes j)

def instantaneousColumn (d : Input n c m) := instantaneousColumnWith d (modeEntries d)

@[simp] theorem instantaneousColumn_entry (d : Input n c m) (i j : State n) :
    entry (instantaneousColumn d j) i = instantaneous d i j := by
  change entry ((j, kineticValue d j) :: compact (perturbationColumn d (modeEntries d) j)) i = _
  rw [entry_cons, entry_compact, perturbationColumn, entry_append, ← add_assoc, ← entry_cons]
  change entry (electronicColumn d j) i + _ = _
  simp only [electronicColumn_entry, inducedColumns,
    entry_flatMap, entry_scale, entry_apply]
  change electronic d i j + ((List.finRange m).map fun k =>
    (-1 / (2 * d.force k)) * ∑ a, entry (vertexColumns d k a) i * entry (vertexColumns d k j) a).sum = _
  simp only [vertexColumns_entry]
  rw [instantaneous_from_square, Fin.sum_univ_def]
  simp [List.sum_neg, sub_eq_add_neg, div_eq_mul_inv, mul_comm, Function.comp_def]

theorem instantaneous_symmetric (d : Input n c m) (h : Valid d) (i j : State n) :
    instantaneous d i j = instantaneous d j i := by
  unfold instantaneous
  rw [electronic_symmetric d h i j]
  simp [mul_comm]

private theorem hop_absSum (p q : Spin n) (j : State n) :
    absSum (hopColumn p q j) ≤ 1 := by
  unfold hopColumn
  have hsign (create : Bool) (t : Spin n) (a b : State n) (s : ℤ)
      (h : step create t a = some (b,s)) : |(s : ℚ)| = 1 := by
    unfold step at h
    split at h
    · contradiction
    · obtain ⟨_, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      simp [abs_pow]
  cases hq : step false q j with
  | none => simp [absSum]
  | some out =>
    obtain ⟨b,t⟩ := out
    cases hp : step true p b with
    | none => simp [hp, absSum]
    | some out =>
      obtain ⟨a,s⟩ := out
      simp [hp, absSum, abs_mul, hsign false q j b t hq, hsign true p b a s hp]

def modeAllowance (terms : List (OrbitalEntry n)) : ℚ :=
  (terms.map fun t => 2 * |t.2.2|).sum

private theorem mode_absSum (terms : List (OrbitalEntry n)) (j : State n) :
    absSum (modeColumns terms j) ≤ modeAllowance terms := by
  induction terms with
  | nil => rfl
  | cons t ts ih =>
    obtain ⟨p,q,a⟩ := t
    simp only [modeColumns, List.flatMap_cons, absSum_append, modeAllowance, List.map_cons,
      List.sum_cons] at ih ⊢
    apply add_le_add _ ih
    rw [absSum_flatMap]
    change absSum (scale a (hopColumn (p,0) (q,0) j)) +
      (absSum (scale a (hopColumn (p,1) (q,1) j)) + 0) ≤ 2 * |a|
    simp only [absSum_scale, add_zero]
    have h (s : Fin 2) := mul_le_mul_of_nonneg_left (hop_absSum (p,s) (q,s) j) (abs_nonneg a)
    linarith [h 0, h 1]

def perturbationAllowance (d : Input n c m) (modes : Fin m → List (OrbitalEntry n)) : ℚ :=
  ((List.finRange m).map fun k => (modeAllowance (modes k))^2 / (2*d.force k)).sum

theorem perturbation_absSum (d : Input n c m) (modes : Fin m → List (OrbitalEntry n))
    (h : Valid d) (hd : d.density = []) (hs : d.scattering = []) (j : State n) :
    absSum (perturbationColumn d modes j) ≤ perturbationAllowance d modes := by
  have hØ : interactionColumn d j = [(j, 0)] := by
    simp [interactionColumn, scatteringColumn, hd, hs]
  rw [perturbationColumn, absSum_append, hØ]
  simp only [absSum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, abs_zero, add_zero, zero_add]
  change absSum (inducedColumns d modes j) ≤ _
  unfold inducedColumns perturbationAllowance
  rw [absSum_flatMap, ← Fin.sum_univ_def, ← Fin.sum_univ_def]
  apply Finset.sum_le_sum
  intro k _
  have hp : 0 < 2 * d.force k := mul_pos (by norm_num) (h.2.2.2.2.1 k).1
  rw [absSum_scale, abs_div, abs_neg, abs_one, abs_of_pos hp]
  have h0 : 0 ≤ modeAllowance (modes k) := (absSum_nonneg _).trans (mode_absSum _ j)
  have ha := (absSum_apply (modeColumns (modes k)) (modeColumns (modes k) j) _ (mode_absSum _)).trans
    (mul_le_mul_of_nonneg_left (mode_absSum _ j) h0)
  rw [pow_two, one_div_mul_eq_div]
  exact div_le_div_of_nonneg_right ha hp.le

end Grain.HarmonicBand
