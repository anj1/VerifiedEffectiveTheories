import Grain.Spinful

/-! The microscopic harmonic Hamiltonian. The variational domain is the union
of finite occupation boxes, so every finitely supported Fock state is allowed. -/

namespace Grain.Phonon

open TwoShell
open scoped BigOperators

def lowQuanta (o : Option Mode) : Mode → ℕ :=
  fun j => if o = some j then 1 else 0

abbrev HigherQuanta (cutoff : ℕ) :=
  { q : Mode → Fin (cutoff + 2) // ∀ o, (fun j => (q j).val) ≠ lowQuanta o }

noncomputable instance (cutoff : ℕ) : Fintype (HigherQuanta cutoff) := Fintype.ofFinite _

abbrev PhononBasis (cutoff : ℕ) := Option Mode ⊕ HigherQuanta cutoff

def quanta {cutoff : ℕ} : PhononBasis cutoff → Mode → ℕ
  | .inl o => lowQuanta o
  | .inr q => fun j => (q.val j).val

theorem quanta_injective (cutoff : ℕ) : Function.Injective (@quanta cutoff) := by
  have low : Function.Injective lowQuanta := by
    intro a b h
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some j =>
        have hj := congrFun h j
        simp [lowQuanta] at hj
    | some i =>
      have hi := congrFun h i
      symm
      show b = some i
      by_contra hn
      simp [lowQuanta, hn] at hi
  intro q p h
  rcases q with o | q <;> rcases p with v | p
  · exact congrArg Sum.inl (low h)
  · exact False.elim (p.property o h.symm)
  · exact False.elim (q.property v h)
  · exact congrArg Sum.inr (Subtype.ext (funext fun j => Fin.ext (congrFun h j)))

/-- Occupation boxes contain all occupation vectors bounded by their cutoff. -/
theorem quanta_covers (cutoff : ℕ) (q : Mode → ℕ) (h : ∀ j, q j < cutoff + 2) :
    ∃ o : PhononBasis cutoff, quanta o = q := by
  by_cases hlow : ∃ o, q = lowQuanta o
  · obtain ⟨o, rfl⟩ := hlow
    exact ⟨Sum.inl o, rfl⟩
  · exact ⟨Sum.inr ⟨fun j => ⟨q j, h j⟩, fun o ho => hlow ⟨o, ho⟩⟩, rfl⟩

theorem finite_support_covered (labels : Finset (Mode → ℕ)) :
    ∃ cutoff : ℕ, ∀ q ∈ labels, ∃ o : PhononBasis cutoff, quanta o = q := by
  let cutoff := ∑ q ∈ labels, ∑ j : Mode, q j
  refine ⟨cutoff, fun q hq => quanta_covers cutoff q ?_⟩
  intro j
  have hj : q j ≤ ∑ i : Mode, q i :=
    Finset.single_le_sum (f := q) (fun i _ => Nat.zero_le (q i)) (Finset.mem_univ j)
  have hq' : (∑ i : Mode, q i) ≤ cutoff :=
    Finset.single_le_sum (f := fun q' : Mode → ℕ => ∑ i : Mode, q' i)
      (fun _ _ => Nat.zero_le _) hq
  exact lt_of_le_of_lt (hj.trans hq') (Nat.lt_add_of_pos_right (by decide))

def addQuantum (j : Mode) (q : Mode → ℕ) : Mode → ℕ :=
  fun i => q i + if i = j then 1 else 0

private theorem vacuum_ne_add (j : Mode) (q : Mode → ℕ) :
    lowQuanta none ≠ addQuantum j q := by
  intro h
  have hj := congrFun h j
  simp [lowQuanta, addQuantum] at hj

private theorem one_eq_add (i j : Mode) (q : Mode → ℕ) :
    lowQuanta (some i) = addQuantum j q ↔ i = j ∧ q = lowQuanta none := by
  constructor
  · intro h
    have hij : i = j := by
      by_contra hn
      have hj := congrFun h j
      simp [lowQuanta, addQuantum, hn] at hj
    subst i
    refine ⟨rfl, funext fun k => ?_⟩
    have hk := congrFun h k
    by_cases hkj : k = j
    · subst k
      simpa [lowQuanta, addQuantum] using hk.symm
    · simpa [lowQuanta, addQuantum, hkj, Ne.symm hkj] using hk.symm
  · rintro ⟨rfl, rfl⟩
    funext k
    simp [lowQuanta, addQuantum, eq_comm]

/-- The annihilation operator in the occupation basis. Each output row
uses the input with one extra quantum and the coefficient `√(q_j+1)`. -/
noncomputable def annihilate {n cutoff : ℕ} (j : Mode)
    (ψ : PhononBasis cutoff → SpinSector n → ℝ) (q : PhononBasis cutoff)
    (a : SpinSector n) : ℝ :=
  ∑ p : PhononBasis cutoff, if quanta p = addQuantum j (quanta q) then
    Real.sqrt (quanta p j) * ψ p a else 0

theorem annihilate_low {n cutoff : ℕ} (x : SpinSector n → ℝ)
    (y : Mode → SpinSector n → ℝ) (j : Mode) :
    annihilate j (lowState (p := HigherQuanta cutoff) x y) = lowAnnihilated y j := by
  funext q a
  simp only [annihilate, Fintype.sum_sum_type, Fintype.sum_option, lowState,
    Sum.elim_inl, Sum.elim_inr, Option.elim'_none, Option.elim'_some, quanta,
    Pi.zero_apply, mul_zero, ite_self, Finset.sum_const_zero, add_zero,
    vacuum_ne_add, ite_false, zero_add, one_eq_add]
  cases q with
  | inl o =>
    cases o with
    | none => cases j <;> simp [lowAnnihilated, lowQuanta]
    | some i =>
      have h : lowQuanta (some i) ≠ lowQuanta none := by
        intro h
        have hi := congrFun h i
        simp [lowQuanta] at hi
      simp [lowAnnihilated, h]
  | inr q => simp [lowAnnihilated, q.property none]

/-- Quadratic form of the fixed-number electron–phonon Hamiltonian in the
occupation box. The kinetic term consists only of one-particle energies. -/
noncomputable def phononHamiltonian (r s : Bool) (k : Fin 3) (cutoff : ℕ)
    (ψ : PhononBasis cutoff → SpinSector (6 + k.val) → ℝ) : ℝ :=
  harmonicForm (kineticForm (Prediction.innerRadius r) (Prediction.outerRadius s))
    vertex frequency mixing annihilate ψ

def microscopicEnergies (r s : Bool) (k : Fin 3) : Set ℝ :=
  ⋃ cutoff : ℕ, normalizedEnergies (phononHamiltonian r s k cutoff)

/-- The ground energy is the Rayleigh infimum over all finite occupation
supports in the fixed-number sector. -/
noncomputable def microscopicGround (r s : Bool) (k : Fin 3) : ℝ :=
  sInf (microscopicEnergies r s k)

end Grain.Phonon
