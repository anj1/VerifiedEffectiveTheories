import Grain.TwoShell

/-! The sparse certificate checker for occupation Hamiltonians. Its residual
checks have the same meaning as the dense quadratic-form tests. -/

namespace Grain.TwoShell

open scoped BigOperators

def rationalLevels (r s : ℚ) : Fin 7 → ℚ := ![-s, -r, -1, 0, 1, r, s]
def coupling : ℚ := 1 / 100

def diagonal (r s : ℚ) (a : Occupation) : ℚ :=
  ∑ i : Fin 7, ((a i).val : ℚ) * rationalLevels r s i - coupling * pairNumber a

def ratH (r s : ℚ) (n : ℕ) (i j : Sector n) : ℚ :=
  if i = j then diagonal r s i.val else if Hop i.val j.val then -coupling else 0

theorem ratH_cast (r s : ℚ) (n : ℕ) (i j : Sector n) :
    (ratH r s n i j : ℝ) = hamiltonian n 1 (r : ℝ) (s : ℝ) (coupling : ℝ) i j := by
  classical
  have hl (k : Fin 7) : (rationalLevels r s k : ℝ) = levels 1 r s k := by
    fin_cases k <;> simp [rationalLevels, levels]
  by_cases hij : i = j
  · subst j
    simp [ratH, hamiltonian, shifted, diagonal, kinetic, hl]
  by_cases hh : Hop i.val j.val <;> simp [ratH, hamiltonian, shifted, hij, hh]

def legal (a : Occupation) (p : Fin 7 × Fin 7) : Prop :=
  a p.1 = 2 ∧ a p.2 = 0

instance (a : Occupation) (p : Fin 7 × Fin 7) : Decidable (legal a p) := by
  unfold legal
  infer_instance

private theorem endpoints_ne {a : Occupation} {p : Fin 7 × Fin 7} (h : legal a p) :
    p.1 ≠ p.2 := by
  intro hp
  have : (2 : Fin 3) = 0 := h.1.symm.trans ((congrArg a hp).trans h.2)
  contradiction

private theorem move_count (a : Occupation) (p : Fin 7 × Fin 7) (h : legal a p) :
    electronCount (move a p.1 p.2) = electronCount a := by
  have hd := endpoints_ne h
  have he : move a p.1 p.2 = a ∘ Equiv.swap p.1 p.2 := by
    funext i
    rcases eq_or_ne i p.1 with rfl | hi
    · simp [move, Function.comp, h.2]
    rcases eq_or_ne i p.2 with rfl | hj
    · simp [move, Function.comp, hd.symm, h.1]
    · simp [move, Function.comp, hi, hj, Equiv.swap_apply_of_ne_of_ne]
  rw [he]
  exact Equiv.sum_comp (Equiv.swap p.1 p.2) (fun i => (a i).val)

private theorem moves_injective (a : Occupation) :
    Function.Injective (fun p : {p // legal a p} => move a p.val.1 p.val.2) := by
  intro p q h
  apply Subtype.ext
  apply Prod.ext
  · by_contra hn
    have hv := congrFun h p.val.1
    have hd : p.val.1 ≠ q.val.2 := by
      intro he
      have : (2 : Fin 3) = 0 := p.property.1.symm.trans ((congrArg a he).trans q.property.2)
      contradiction
    simp [move, hn, hd, p.property.1] at hv
  · by_contra hn
    have hv := congrFun h p.val.2
    have hd : p.val.2 ≠ q.val.1 := by
      intro he
      have : (0 : Fin 3) = 2 := p.property.2.symm.trans ((congrArg a he).trans q.property.1)
      contradiction
    simp [move, (endpoints_ne p.property).symm, hn, hd, p.property.2] at hv

noncomputable def neighbors {n : ℕ} (i : Sector n) :
    {p // legal i.val p} ≃ {j : Sector n // Hop i.val j.val} :=
  Equiv.ofBijective (fun p =>
    ⟨⟨move i.val p.val.1 p.val.2, (move_count i.val p.val p.property).trans i.property⟩,
      ⟨p.val.1, p.val.2, p.property.1, p.property.2, rfl⟩⟩) <| by
    constructor
    · intro p q h
      exact moves_injective i.val (congrArg (fun j : {j : Sector n // Hop i.val j.val} =>
        j.val.val) h)
    · intro j
      obtain ⟨src, dst, hs, hd, he⟩ := j.property
      exact ⟨⟨(src, dst), hs, hd⟩, Subtype.ext (Subtype.ext he.symm)⟩

private theorem Hop.ne {a b : Occupation} (h : Hop a b) : a ≠ b := by
  obtain ⟨src, dst, hs, _, rfl⟩ := h
  intro he
  have hv := congrFun he src
  simp [move, hs] at hv

def sparseAction (r s : ℚ) (w : Occupation → ℚ) (a : Occupation) : ℚ :=
  diagonal r s a * w a - coupling *
    ∑ p : Fin 7 × Fin 7, if legal a p then w (move a p.1 p.2) else 0

theorem sparseAction_eq (r s : ℚ) {n : ℕ} (w : Occupation → ℚ) (i : Sector n) :
    action (ratH r s n) (fun j => w j.val) i = sparseAction r s w i.val := by
  classical
  have hsplit (j : Sector n) : ratH r s n i j * w j.val =
      (if i = j then diagonal r s i.val * w i.val else 0) -
        (if Hop i.val j.val then coupling * w j.val else 0) := by
    rcases eq_or_ne i j with rfl | hne
    · have h : ¬ Hop i.val i.val := fun hh => hh.ne rfl
      simp [ratH, h]
    · by_cases h : Hop i.val j.val <;> simp [ratH, hne, h, neg_mul]
  simp only [action, hsplit, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  unfold sparseAction
  congr 1
  rw [Finset.mul_sum]
  simp_rw [mul_ite, mul_zero]
  rw [← Finset.sum_filter, ← Finset.sum_filter,
    ← Finset.sum_subtype_eq_sum_filter, ← Finset.sum_subtype_eq_sum_filter]
  have h₁ : Finset.univ.subtype (fun j : Sector n => Hop i.val j.val) = Finset.univ :=
    Finset.eq_univ_of_forall fun j => Finset.mem_subtype.mpr (Finset.mem_univ j.val)
  have h₂ : Finset.univ.subtype (legal i.val) = Finset.univ :=
    Finset.eq_univ_of_forall fun j => Finset.mem_subtype.mpr (Finset.mem_univ j.val)
  rw [h₁, h₂]
  exact ((neighbors i).sum_comp (fun j => coupling * w j.val.val)).symm

/-- Certificate vectors are stored by ternary occupation code. -/
def code (a : Occupation) : ℕ := ∑ i : Fin 7, (a i).val * 3 ^ i.val

def decode (k : ℕ) : Occupation := fun i =>
  ⟨k / 3 ^ i.val % 3, Nat.mod_lt _ (by decide)⟩

private theorem code_le (a : Occupation) : code a < 2187 := by
  have h (i : Fin 7) : (a i).val ≤ 2 := by omega
  have hs : code a ≤ ∑ i : Fin 7, 2 * 3 ^ i.val := by
    exact Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_right _ (h i))
  exact hs.trans_lt (by decide +kernel)

private theorem decode_code (a : Occupation) : decode (code a) = a := by
  have h (i : Fin 7) : (a i).val < 3 := (a i).isLt
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  have h5 := h 5
  have h6 := h 6
  funext i
  apply Fin.ext
  fin_cases i <;>
    norm_num [decode, code, Fin.sum_univ_succ, Fin.val_succ] <;> omega

theorem for_all_occupations {P : Occupation → Prop}
    (h : ∀ k : Fin 2187, P (decode k.val)) (a : Occupation) : P a := by
  simpa only [decode_code] using h ⟨code a, code_le a⟩

/-- The low-energy block in each sector has the same singly occupied sites as
the free reference. Pair transfers preserve that set. -/
def active (n : ℕ) (a : Occupation) : Prop := ∀ i, a i = 1 ↔ n = 7 ∧ i = 3

instance (n : ℕ) (a : Occupation) : Decidable (active n a) := by
  unfold active
  infer_instance

private theorem active_move (n : ℕ) (a : Occupation) (p : Fin 7 × Fin 7) (h : legal a p) :
    active n (move a p.1 p.2) ↔ active n a := by
  have hi := endpoints_ne h
  have hp (i : Fin 7) : (move a p.1 p.2 i = 1) ↔ (a i = 1) := by
    rcases eq_or_ne i p.1 with rfl | h₁
    · simp [move, h.1]
    rcases eq_or_ne i p.2 with rfl | h₂
    · simp [move, hi.symm, h.2]
    · simp [move, h₁, h₂]
  simp only [active, hp]

structure ShellWitness where
  lo : ℚ
  hi : ℚ
  weights : List (ℕ × ℕ)

def amplitude (w : ShellWitness) (a : Occupation) : ℚ :=
  ((w.weights.lookup (code a)).getD 0 : ℕ)

def lowerVector (n : ℕ) (w : ShellWitness) (a : Occupation) : ℚ :=
  if active n a then amplitude w a else 1

def trialVector (n : ℕ) (w : ShellWitness) (a : Occupation) : ℚ :=
  if active n a then amplitude w a else 0

def rowTest (r s : ℚ) (n : ℕ) (w : ShellWitness) (a : Occupation) : Prop :=
  if electronCount a = n then
    if active n a then
      0 < amplitude w a ∧
      w.lo * amplitude w a ≤ sparseAction r s (amplitude w) a ∧
      sparseAction r s (amplitude w) a ≤ w.hi * amplitude w a
    else w.lo ≤ diagonal r s a - 49 * coupling
  else True

instance (r s : ℚ) (n : ℕ) (w : ShellWitness) (a : Occupation) :
    Decidable (rowTest r s n w a) := by
  unfold rowTest
  infer_instance

/-- Partition the code range into short chunks so checking requires only
bounded recursion, including in the kernel. -/
def checkRange (r s : ℚ) (n : ℕ) (w : ShellWitness) (chunk : Fin 27) : Prop :=
  ∀ offset : Fin 81, rowTest r s n w (decode (81 * chunk.val + offset.val))

instance (r s : ℚ) (n : ℕ) (w : ShellWitness) (chunk : Fin 27) :
    Decidable (checkRange r s n w chunk) := by
  unfold checkRange
  infer_instance

theorem rows_from_chunks (r s : ℚ) (n : ℕ) (w : ShellWitness)
    (h : ∀ chunk, checkRange r s n w chunk) (a : Occupation) : rowTest r s n w a := by
  apply for_all_occupations (a := a)
  intro k
  have hk := k.isLt
  have hq : k.val / 81 < 27 := by omega
  have hr : k.val % 81 < 81 := Nat.mod_lt _ (by decide)
  have ht := h ⟨k.val / 81, hq⟩ ⟨k.val % 81, hr⟩
  have he : 81 * (k.val / 81) + k.val % 81 = k.val := by omega
  simpa only [he] using ht

private theorem sparse_on_active (r s : ℚ) (n : ℕ) (w : ShellWitness) (a : Occupation)
    (ha : active n a) (u : ℚ) :
    sparseAction r s (fun b => if active n b then amplitude w b else u) a =
      sparseAction r s (amplitude w) a := by
  unfold sparseAction
  simp only [ha, ite_true]
  congr 2
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : legal a p
  · simp [hp, (active_move n a p hp).2 ha]
  · simp [hp]

private theorem sparse_inactive_lower (r s : ℚ) (n : ℕ) (w : ShellWitness) (a : Occupation)
    (ha : ¬ active n a) : diagonal r s a - 49 * coupling ≤
      sparseAction r s (lowerVector n w) a := by
  have h (p : Fin 7 × Fin 7) :
      (if legal a p then lowerVector n w (move a p.1 p.2) else 0) ≤ 1 := by
    by_cases hp : legal a p
    · have hn : ¬ active n (move a p.1 p.2) := fun h => ha ((active_move n a p hp).1 h)
      simp [hp, lowerVector, hn]
    · simp [hp]
  have hs : (∑ p : Fin 7 × Fin 7,
      if legal a p then lowerVector n w (move a p.1 p.2) else 0) ≤ 49 := by
    exact (Finset.sum_le_sum (fun p _ => h p)).trans (by norm_num)
  unfold sparseAction
  rw [show lowerVector n w a = 1 by simp [lowerVector, ha], mul_one]
  nlinarith only [mul_le_mul_of_nonneg_left hs (show 0 ≤ coupling by norm_num [coupling])]

private theorem rationalNormSq_pos {ι : Type} [Fintype ι] (w : ι → ℚ)
    (i : ι) (hi : 0 < w i) : 0 < rationalNormSq w := by
  unfold rationalNormSq
  exact (sq_pos_of_pos hi).trans_le
    (Finset.single_le_sum (fun j _ => sq_nonneg (w j)) (Finset.mem_univ i))

theorem witness_bounds (r s : ℚ) (n : ℕ) (w : ShellWitness)
    (hrows : ∀ chunk, checkRange r s n w chunk)
    (support : ∃ a : Occupation, electronCount a = n ∧ active n a) :
    (w.lo : ℝ) ≤ ground (ratH r s n) ∧ ground (ratH r s n) ≤ (w.hi : ℝ) := by
  let A := ratH r s n
  let wl : Sector n → ℚ := fun i => lowerVector n w i.val
  let wt : Sector n → ℚ := fun i => trialVector n w i.val
  have hsym (i j : Sector n) : A i j = A j i := by
    have he := hamiltonian_symmetric n 1 (r : ℝ) (s : ℝ) (coupling : ℝ) i j
    rw [← ratH_cast, ← ratH_cast] at he
    exact_mod_cast he
  have hsign (i j : Sector n) (hij : i ≠ j) : A i j ≤ 0 := by
    by_cases hh : Hop i.val j.val <;> norm_num [A, ratH, hij, hh, coupling]
  have activeRows (i : Sector n) (ha : active n i.val) :
      0 < amplitude w i.val ∧
        w.lo * amplitude w i.val ≤ sparseAction r s (amplitude w) i.val ∧
        sparseAction r s (amplitude w) i.val ≤ w.hi * amplitude w i.val := by
    simpa only [rowTest, i.property, ite_true, ite_eq_left ha] using
      rows_from_chunks r s n w hrows i.val
  have hpos (i : Sector n) : 0 < wl i := by
    by_cases ha : active n i.val
    · simpa only [wl, lowerVector, ite_eq_left ha] using (activeRows i ha).1
    · simp [wl, lowerVector, ha]
  have hlo (i : Sector n) : w.lo * wl i ≤ action A wl i := by
    show w.lo * lowerVector n w i.val ≤ action (ratH r s n) _ i
    rw [sparseAction_eq]
    by_cases ha : active n i.val
    · rw [show lowerVector n w i.val = amplitude w i.val by simp [lowerVector, ha]]
      exact (activeRows i ha).2.1.trans_eq (sparse_on_active r s n w i.val ha 1).symm
    · have hb : w.lo ≤ diagonal r s i.val - 49 * coupling := by
        simpa only [rowTest, i.property, ite_true, ite_eq_right ha] using
          rows_from_chunks r s n w hrows i.val
      simpa only [lowerVector, ite_eq_right ha, mul_one] using
        hb.trans (sparse_inactive_lower r s n w i.val ha)
  have hu : rayleighNumerator A wt ≤ w.hi * rationalNormSq wt := by
    rw [rayleighNumerator, rationalNormSq, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    by_cases ha : active n i.val
    · have hr := (activeRows i ha).2.2
      change wt i * action (ratH r s n) (fun j => trialVector n w j.val) i ≤ _
      rw [sparseAction_eq]
      rw [show sparseAction r s (trialVector n w) i.val = sparseAction r s (amplitude w) i.val from
        sparse_on_active r s n w i.val ha 0]
      simp only [wt, trialVector, ite_eq_left ha]
      nlinarith only [mul_le_mul_of_nonneg_left hr (activeRows i ha).1.le]
    · simp [wt, trialVector, ha]
  obtain ⟨a, hnum, ha⟩ := support
  let i : Sector n := ⟨a, hnum⟩
  have ht : 0 < rationalNormSq wt :=
    rationalNormSq_pos wt i (by change 0 < trialVector n w a; simpa [trialVector, ha] using (activeRows i ha).1)
  exact ground_bounds A w.lo w.hi (weighted_lower A wl w.lo hsym hsign hpos hlo)
    (normalized_trial A wt ht w.hi hu)

end Grain.TwoShell
