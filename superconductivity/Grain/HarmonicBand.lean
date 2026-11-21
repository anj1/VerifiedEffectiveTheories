import Grain.EFTBounds

/-! Reconstruction of a finite real spin-degenerate band from screened
electronic interactions and mass-weighted DFPT derivatives. Energies are in
meV, with ℏ = 1 and the oscillator zero-point energies omitted. -/

namespace Grain.HarmonicBand

open Phonon

abbrev Orbital (n : ℕ) := Fin n
abbrev Spin (n : ℕ) := Fin n × Fin 2
abbrev State (n : ℕ) := Fin (2 ^ (2 * n))
abbrev Derivative (n : ℕ) := List (Orbital n × Orbital n × ℚ)

structure Density (n : ℕ) where
  first : Spin n
  second : Spin n
  strength : ℚ

structure Scattering (n : ℕ) where
  create : Spin n × Spin n
  annihilate : Spin n × Spin n
  strength : ℚ
  deriving DecidableEq

inductive Vertex (n c : ℕ) where
  | projected (derivative : Derivative n)
  | cartesian (polarization : Fin c → ℚ)

structure Input (n c m : ℕ) where
  levels : Orbital n → ℚ
  density : List (Density n)
  scattering : List (Scattering n)
  screeningConvention : String
  cartesian : Fin c → Derivative n
  force : Fin m → ℚ
  vertex : Fin m → Vertex n c

variable {n c m : ℕ}

def slot (s : Spin n) : ℕ := 2 * s.1.val + s.2.val

def occupied (a : State n) (s : Spin n) : Bool := a.val.testBit (slot s)

/-- The phase counts occupied spin orbitals strictly before the operated slot. -/
def step (create : Bool) (s : Spin n) (a : State n) : Option (State n × ℤ) :=
  if occupied a s == create then none
  else some (Fin.ofNat _ (a.val ^^^ 2 ^ slot s),
    (-1) ^ (List.range (slot s)).countP a.val.testBit)

/-- The word is written in operator product order, with its rightmost
operator acting first. -/
def applyWord (word : List (Bool × Spin n)) (a : State n) : Option (State n × ℤ) :=
  word.foldrM (fun (create, s) (b, sign) => do
    let (d, next) ← step create s b
    return (d, sign * next)) (a, 1)

abbrev Column (n : ℕ) := List (State n × ℚ)

private def signedTransition (a : State n) (strength : ℚ)
    (word : List (Bool × Spin n)) : Option (State n × ℚ) :=
  (applyWord word a).map fun (target, sign) => (target, strength * sign)

def columnEntry (col : Column n) (i : State n) : ℚ :=
  ((col.filter fun t => t.1 == i).map Prod.snd).sum

/-- The entry of `c†ₚ c_q` is the overlap of two signed annihilation
results. This implements creation as the adjoint of annihilation. -/
def annihilationOverlap (p q : Spin n) (i j : State n) : ℚ :=
  match step false p i, step false q j with
  | some (a, left), some (b, right) => if a = b then (left : ℚ) * right else 0
  | _, _ => 0

def oneBody (a : Orbital n → Orbital n → ℚ) (i j : State n) : ℚ :=
  ∑ p, ∑ q, ∑ s : Fin 2, a p q * annihilationOverlap (p, s) (q, s) i j

private theorem overlap_swap (p q : Spin n) (i j : State n) :
    annihilationOverlap p q i j = annihilationOverlap q p j i := by
  unfold annihilationOverlap
  cases step false p i with
  | none => cases step false q j <;> rfl
  | some left =>
    cases step false q j with
    | none => cases left; rfl
    | some right =>
      rcases left with ⟨a, sa⟩
      rcases right with ⟨b, sb⟩
      simp [eq_comm (a := a) (b := b), mul_comm]

private theorem oneBody_symmetric (a : Orbital n → Orbital n → ℚ)
    (h : ∀ p q, a p q = a q p) (i j : State n) : oneBody a i j = oneBody a j i := by
  unfold oneBody
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro s _
  rw [h q p, overlap_swap (q, s) (p, s) i j]

def kinetic (d : Input n c m) (i j : State n) : ℚ :=
  if i = j then ∑ p : Orbital n, ∑ s : Fin 2,
    if occupied j (p, s) then d.levels p else 0
  else 0

def scatteringColumn (d : Input n c m) (j : State n) : Column n :=
  d.scattering.filterMap fun t => signedTransition j t.strength
    [(true, t.create.1), (true, t.create.2), (false, t.annihilate.1), (false, t.annihilate.2)]

def screened (d : Input n c m) (i j : State n) : ℚ :=
  (if i = j then ((d.density.filter fun t =>
    occupied j t.first && occupied j t.second).map Density.strength).sum else 0) +
  columnEntry (scatteringColumn d j) i

def electronic (d : Input n c m) (i j : State n) : ℚ := kinetic d i j + screened d i j

def derivativeEntry (a : Derivative n) (p q : Orbital n) : ℚ :=
  ((a.filter fun t => t.1 == min p q && t.2.1 == max p q).map (·.2.2)).sum

def modeEntry (d : Input n c m) (mode : Fin m) (p q : Orbital n) : ℚ :=
  match d.vertex mode with
  | .projected a => derivativeEntry a p q
  | .cartesian v => ∑ a, v a * derivativeEntry (d.cartesian a) p q

def electronPhonon (d : Input n c m) (mode : Fin m) (i j : State n) : ℚ :=
  oneBody (modeEntry d mode) i j

theorem electronPhonon_symmetric (d : Input n c m) (mode : Fin m)
    (i j : State n) : electronPhonon d mode i j = electronPhonon d mode j i := by
  apply oneBody_symmetric
  intro p q
  unfold modeEntry
  split <;> simp only [derivativeEntry, min_comm p q, max_comm p q]

def validDerivative (a : Derivative n) : Prop :=
  (a.all fun t => t.1 ≤ t.2.1) = true ∧ (a.map fun t => (t.1, t.2.1)).Nodup

instance (a : Derivative n) : Decidable (validDerivative a) := by
  unfold validDerivative
  infer_instance

def validMode (d : Input n c m) (j : Fin m) : Prop :=
  match d.vertex j with
  | .projected a => validDerivative a
  | .cartesian v => (∑ i, v i ^ 2) = 1

instance (d : Input n c m) (j : Fin m) : Decidable (validMode d j) := by
  unfold validMode
  split <;> infer_instance

def orthogonalModes (d : Input n c m) (j k : Fin m) : Prop :=
  match d.vertex j, d.vertex k with
  | .cartesian v, .cartesian w => (∑ i, v i * w i) = 0
  | _, _ => True

instance (d : Input n c m) (j k : Fin m) : Decidable (orthogonalModes d j k) := by
  unfold orthogonalModes
  split <;> infer_instance

private def symmetricColumns (columns : State n → Column n) : Prop :=
  ∀ j, ((columns j).all fun (i, _) => columnEntry (columns j) i == columnEntry (columns i) j) = true

private instance (columns : State n → Column n) : Decidable (symmetricColumns columns) := by
  unfold symmetricColumns
  infer_instance

private theorem entry_eq_zero {col : Column n} {i : State n}
    (h : ∀ t ∈ col, t.1 ≠ i) : columnEntry col i = 0 := by
  have hempty : (col.filter fun t => t.1 == i) = [] := by
    rw [List.filter_eq_nil_iff]
    intro t ht
    simp [h t ht]
  simp [columnEntry, hempty]

private theorem column_symmetry {columns : State n → Column n} (h : symmetricColumns columns)
    (i j : State n) : columnEntry (columns j) i = columnEntry (columns i) j := by
  by_cases hij : ∃ t ∈ columns j, t.1 = i
  · obtain ⟨⟨k, x⟩, ht, rfl⟩ := hij
    simpa using (List.all_eq_true.mp (h j)) (k, x) ht
  by_cases hji : ∃ t ∈ columns i, t.1 = j
  · obtain ⟨⟨k, x⟩, ht, rfl⟩ := hji
    symm
    simpa using (List.all_eq_true.mp (h i)) (k, x) ht
  · rw [entry_eq_zero (fun t ht he => hij ⟨t, ht, he⟩),
      entry_eq_zero (fun t ht he => hji ⟨t, ht, he⟩)]

/-- Checks on the exact export, including self-adjointness in Fock space. -/
def Valid (d : Input n c m) : Prop :=
  0 < n ∧ 0 < d.screeningConvention.length ∧
  (d.density.all fun t => t.first != t.second) = true ∧
  (∀ i, validDerivative (d.cartesian i)) ∧
  (∀ j, 0 < d.force j ∧ validMode d j) ∧
  (∀ j k, j ≠ k → orthogonalModes d j k) ∧
  (d.scattering = [] ∨ symmetricColumns (scatteringColumn d))

instance (d : Input n c m) : Decidable (Valid d) := by
  unfold Valid
  infer_instance

theorem electronic_symmetric (d : Input n c m) (h : Valid d) (i j : State n) :
    electronic d i j = electronic d j i := by
  by_cases hij : i = j
  · subst j
    rfl
  · obtain ⟨_, _, _, _, _, _, hempty | hscattering⟩ := h
    · simp [electronic, kinetic, screened, scatteringColumn, columnEntry, hempty, hij, Ne.symm hij]
    · simpa [electronic, kinetic, screened, hij, Ne.symm hij] using column_symmetry hscattering i j

/-- Use the Gram matrix of the signed one-body vertex. For a validated
export this is the square of the self-adjoint vertex. -/
def instantaneous (d : Input n c m) (i j : State n) : ℚ :=
  electronic d i j - ∑ k, (∑ a, electronPhonon d k a i * electronPhonon d k a j) / (2 * d.force k)

theorem instantaneous_from_square (d : Input n c m) (i j : State n) :
    instantaneous d i j = electronic d i j -
      ∑ k, (∑ a, electronPhonon d k i a * electronPhonon d k a j) / (2 * d.force k) := by
  unfold instantaneous
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  exact Finset.sum_congr rfl fun a _ =>
    congrArg (· * electronPhonon d k a j) (electronPhonon_symmetric d k a i)

noncomputable def act (A : State n → State n → ℚ) (x : State n → ℝ) (i : State n) : ℝ :=
  ∑ j, (A i j : ℝ) * x j

private theorem gram_form (A : State n → State n → ℚ) (x : State n → ℝ) :
    form (fun i j => ∑ a, A a i * A a j) x = normSq (act A x) := by
  let t (i j a : State n) : ℝ := (A a i : ℝ) * (A a j : ℝ) * (x i * x j)
  simp only [form, normSq, act, pow_two, Rat.cast_sum, Rat.cast_mul,
    Finset.sum_mul, Finset.mul_sum]
  calc
    _ = ∑ i, ∑ a, ∑ j, t i j a := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ a, ∑ i, ∑ j, t i j a := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      dsimp [t]
      ring

theorem instantaneous_form (d : Input n c m) (x : State n → ℝ) :
    form (instantaneous d) x = form (electronic d) x -
      ∑ k, normSq (act (electronPhonon d k) x) / (2 * (d.force k : ℝ)) := by
  rw [show instantaneous d = (fun i j => electronic d i j -
    ∑ k, (∑ a, electronPhonon d k a i * electronPhonon d k a j) / (2 * d.force k)) from rfl,
    form_sub]
  congr 1
  conv_rhs => enter [2, k]; rw [← gram_form]
  let a (k : Fin m) (i j : State n) : ℝ :=
    ∑ b, (electronPhonon d k b i : ℝ) * (electronPhonon d k b j : ℝ)
  let f (k : Fin m) : ℝ := 2 * (d.force k : ℝ)
  simp only [form, Rat.cast_sum, Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Finset.sum_mul]
  conv_rhs => simp only [← Finset.sum_mul]
  change (∑ i, ∑ j, ∑ k, a k i j / f k * (x i * x j)) =
    ∑ k, (∑ i, ∑ j, a k i j * (x i * x j)) / f k
  calc
    _ = ∑ i, ∑ k, ∑ j, a k i j / f k * (x i * x j) :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ j, a k i j / f k * (x i * x j) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      simp only [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

noncomputable def frequency (d : Input n c m) (j : Fin m) : ℝ := Real.sqrt (d.force j)

/-- Coefficient of the mass-weighted derivative in the oscillator vertex. -/
noncomputable def coupling (d : Input n c m) (j : Fin m) : ℝ :=
  1 / Real.sqrt (2 * frequency d j)

private theorem force_pos (d : Input n c m) (h : Valid d) (j : Fin m) :
    0 < (d.force j : ℝ) := by
  obtain ⟨_, _, _, _, hforce, _, _⟩ := h
  exact_mod_cast (hforce j).1

theorem frequency_pos (d : Input n c m) (h : Valid d) (j : Fin m) :
    0 < frequency d j :=
  Real.sqrt_pos.2 (force_pos d h j)

theorem displacement_coefficient (d : Input n c m) (h : Valid d) (j : Fin m) :
    frequency d j * (coupling d j / frequency d j) ^ 2 = 1 / (2 * (d.force j : ℝ)) := by
  have hp := frequency_pos d h j
  have hsq : frequency d j ^ 2 = (d.force j : ℝ) := by
    exact Real.sq_sqrt (force_pos d h j).le
  rw [← hsq, coupling, div_pow, div_pow, one_pow, Real.sq_sqrt (by positivity)]
  field_simp

/-- Each mode has occupation labels from zero through the cutoff. -/
abbrev Quanta (m cutoff : ℕ) := Fin m → Fin (cutoff + 1)

theorem occupation_box_covers (labels : Finset (Fin m → ℕ)) :
    ∃ cutoff, ∀ q ∈ labels, ∃ p : Quanta m cutoff, ∀ j, (p j).val = q j := by
  classical
  refine ⟨∑ q ∈ labels, ∑ j, q j, fun q hq => ?_⟩
  have hmode (j : Fin m) : q j ≤ ∑ k, q k :=
    Finset.single_le_sum (fun k _ => Nat.zero_le (q k)) (Finset.mem_univ j)
  have htotal : (∑ j, q j) ≤ ∑ p ∈ labels, ∑ j, p j :=
    Finset.single_le_sum (f := fun p => ∑ j, p j) (fun _ _ => Nat.zero_le _) hq
  exact ⟨fun j => ⟨q j, Nat.lt_succ_of_le ((hmode j).trans htotal)⟩, fun _ => rfl⟩

noncomputable def annihilate {cutoff : ℕ}
    (j : Fin m) (ψ : Quanta m cutoff → State n → ℝ) (q : Quanta m cutoff) (i : State n) : ℝ :=
  if h : (q j).val + 1 < cutoff + 1 then
    Real.sqrt ((q j).val + 1) * ψ (Function.update q j ⟨(q j).val + 1, h⟩) i
  else 0

/-- Harmonic parent quadratic form with the physical oscillator vertex.
Every finite-support oscillator vector fits in some occupation box. -/
noncomputable def harmonicForm {cutoff : ℕ}
    (d : Input n c m) (ψ : Quanta m cutoff → State n → ℝ) : ℝ :=
  ∑ q, (form (electronic d) (ψ q) + ∑ k,
    (frequency d k * normSq (annihilate k ψ q) +
      2 * coupling d k * inner (annihilate k ψ q) (act (electronPhonon d k) (ψ q))))

/-- The instantaneous electronic form bounds the harmonic form from below
on every occupation box, with no cutoff-dependent error. -/
theorem harmonic_lower {cutoff : ℕ}
    (d : Input n c m) (h : Valid d) (ψ : Quanta m cutoff → State n → ℝ) :
    (∑ q, form (instantaneous d) (ψ q)) ≤ harmonicForm d ψ := by
  unfold harmonicForm
  apply Finset.sum_le_sum
  intro q _
  have hp (j : Fin m) := frequency_pos d h j
  have hs := EFT.mode_squares (frequency d) (fun j => coupling d j / frequency d j)
    (fun j => act (electronPhonon d j) (ψ q)) (fun j => annihilate j ψ q)
  have hc (j : Fin m) : 2 * frequency d j * (coupling d j / frequency d j) =
      2 * coupling d j := by field_simp [(hp j).ne']
  simp_rw [hc, displacement_coefficient d h, one_div_mul_eq_div] at hs
  rw [instantaneous_form, hs]
  have hnonneg := Finset.sum_nonneg (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) =>
    mul_nonneg (hp j).le (normSq_nonneg
      (fun i => annihilate j ψ q i +
        (coupling d j / frequency d j) * act (electronPhonon d j) (ψ q) i)))
  linarith

end Grain.HarmonicBand
