import Grain.DFPTCertificate
import Grain.DFPTReduction

/-! Assemble shell components from a primitive export and replay the spectral bracket. -/

namespace Grain.HarmonicBand

open Phonon Sparse EFT
open scoped BigOperators

variable {n c m b : ℕ}

structure ShellBlock (n : ℕ) where
  p : ℕ
  q : ℕ
  kept : Fin p → State n
  discarded : Fin q → State n
  A : Fin p → Fin p → ℚ
  B : Fin q → Fin p → ℚ
  D : Fin q → Fin q → ℚ

def ShellBlock.state (v : ShellBlock n) : Fin v.p ⊕ Fin v.q → State n :=
  Sum.elim v.kept v.discarded

def ShellBlock.matrix (v : ShellBlock n) := shellMatrix v.A v.B v.D

def ShellBlock.liftedAt (v : ShellBlock n) (z : ℚ) (W : Fin v.q → Fin v.p → ℚ) :=
  lifted (shift v.A z) v.B (shift v.D z) W

def ShellBlock.matrixCheck (v : ShellBlock n)
    (columns : State n → Vector (State n)) : Prop :=
  ∀ i j, v.matrix i j = entry (columns (v.state j)) (v.state i)

instance (v : ShellBlock n) (columns : State n → Vector (State n)) :
    Decidable (v.matrixCheck columns) := by unfold ShellBlock.matrixCheck; infer_instance

def ShellBlock.indexCheck (v : ShellBlock n) (N : ℕ) (part : State n → Option (Fin b))
    (k : Fin b) : Prop :=
  Function.Injective v.state ∧ ∀ i, inSector N (v.state i) = true ∧ part (v.state i) = some k

instance (v : ShellBlock n) (N : ℕ) (part : State n → Option (Fin b)) (k : Fin b) :
    Decidable (v.indexCheck N part k) := by
  unfold ShellBlock.indexCheck Function.Injective
  infer_instance

def shellRowCheck (columns : State n → Vector (State n)) (N : ℕ)
    (blocks : Fin b → ShellBlock n) (part : State n → Option (Fin b)) (l u : ℚ)
    (j : State n) : Prop :=
  match part j with
  | none => if inSector N j then rowTest (columns j) (fun _ => 1) u j else True
  | some k => (∃ i, (blocks k).state i = j) ∧
      ((columns j).all fun t => decide (part t.1 = some k)) = true ∧ rowTest (columns j) (fun _ => 1) l j

instance (columns : State n → Vector (State n)) (N : ℕ) (blocks : Fin b → ShellBlock n)
    (part : State n → Option (Fin b)) (l u : ℚ) (j : State n) :
    Decidable (shellRowCheck columns N blocks part l u j) := by
  unfold shellRowCheck
  split <;> infer_instance

/-- The assembly allowance can discharge a high-energy row outside the live blocks. -/
def shellRowFast (d : Input n c m) (modes : Fin m → List (OrbitalEntry n)) (N : ℕ)
    (blocks : Fin b → ShellBlock n) (part : State n → Option (Fin b)) (l u : ℚ)
    (j : State n) : Prop :=
  if part j = none ∧ inSector N j = true ∧ d.density = [] ∧ d.scattering = [] ∧
      u + perturbationAllowance d modes ≤ kineticValue d j then True
  else shellRowCheck (sectorColumn d modes N u) N blocks part l u j

instance (d : Input n c m) (modes : Fin m → List (OrbitalEntry n)) (N : ℕ)
    (blocks : Fin b → ShellBlock n) (part : State n → Option (Fin b)) (l u : ℚ)
    (j : State n) : Decidable (shellRowFast d modes N blocks part l u j) := by
  unfold shellRowFast
  infer_instance

theorem shellRows_of_fast (d : Input n c m) (hd : Valid d)
    (modes : Fin m → List (OrbitalEntry n)) (N : ℕ)
    (blocks : Fin b → ShellBlock n) (part : State n → Option (Fin b)) (l u : ℚ)
    (hrows : ∀ j, shellRowFast d modes N blocks part l u j) :
    ∀ j, shellRowCheck (sectorColumn d modes N u) N blocks part l u j := by
  intro j
  have h := hrows j
  unfold shellRowFast at h
  split at h
  · rename_i hfast
    obtain ⟨hp, hn, hinter, hscatter, hk⟩ := hfast
    simp only [shellRowCheck, hp, hn, ite_true, sectorColumn, instantaneousColumnWith, List.filter_cons]
    apply rowTest_kinetic _ _ _ _ (perturbationAllowance d modes)
    · norm_num
    · intro i
      exact le_rfl
    · exact (absSum_filter _ _).trans ((absSum_compact _).trans
        (perturbation_absSum d _ hd hinter hscatter j))
    · simpa using hk
  · exact h

private theorem rowTest_mono {ι : Type} [DecidableEq ι] (v : Vector ι) (i : ι) {l u : ℚ}
    (h : l ≤ u) (r : rowTest v (fun _ => 1) u i) : rowTest v (fun _ => 1) l i := by
  refine ⟨r.1, ?_⟩
  have hr := r.2
  simp only [mul_one] at hr ⊢
  linarith

private theorem off_block {ι α : Type} [DecidableEq ι] [DecidableEq α]
    (columns : ι → Vector ι) (part : ι → α) (i j : ι)
    (h : (columns j).all (fun t => decide (part t.1 = part j)) = true) (hne : part i ≠ part j) :
    entry (columns j) i = 0 := by
  have hz : (columns j).filter (fun k => decide (part k.1 = part j)) = columns j :=
    List.filter_eq_self.mpr (List.all_eq_true.mp h)
  rw [← hz, entry_filter _ (fun a => decide (part a = part j))]
  simp [hne]

private noncomputable def mask {ι α : Type} [DecidableEq α]
    (part : ι → α) (k : α) (x : ι → ℝ) (i : ι) : ℝ :=
  if part i = k then x i else 0

private theorem partition_lower {ι α : Type} [Fintype ι] [Fintype α] [DecidableEq α]
    (A : ι → ι → ℚ) (part : ι → α)
    (hzero : ∀ i j, part i ≠ part j → A i j = 0) (l : ℝ) (x : ι → ℝ)
    (h : ∀ k, l * normSq (mask part k x) ≤ form A (mask part k x)) :
    l * normSq x ≤ form A x := by
  have hn : (∑ k, normSq (mask part k x)) = normSq x := by
    unfold normSq
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simp [mask, eq_comm]
  have hf : (∑ k, form A (mask part k x)) = form A x := by
    unfold form
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : part i = part j
    · simp [mask, hij, apply_ite, eq_comm (a := part j)]
    · simp [hzero i j hij]
  have hsum := Finset.sum_le_sum fun k (_ : k ∈ (Finset.univ : Finset α)) => h k
  rwa [← Finset.mul_sum, hn, hf] at hsum

private theorem sum_on_block {ι β α : Type} [Fintype ι] [Fintype β]
    (f : β → ι) (hf : Function.Injective f) (part : ι → α) (k : α)
    (hcover : ∀ i, part i = k → ∃ j, f j = i)
    (g : ι → ℝ) (hg : ∀ i, part i ≠ k → g i = 0) :
    (∑ i, g i) = ∑ j, g (f j) := by
  classical
  rw [← Finset.sum_image (fun _ _ _ _ h => hf h)]
  apply (Finset.sum_subset (Finset.subset_univ _ ) ?_).symm
  intro i _ hi
  apply hg i
  intro hk
  obtain ⟨j, rfl⟩ := hcover i hk
  exact hi (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)

private theorem masked_norm {ι β α : Type} [Fintype ι] [Fintype β] [DecidableEq α]
    (f : β → ι) (hf : Function.Injective f) (part : ι → α) (k : α)
    (hin : ∀ j, part (f j) = k) (hcover : ∀ i, part i = k → ∃ j, f j = i)
    (x : ι → ℝ) :
    normSq (mask part k x) = normSq (x ∘ f) := by
  unfold normSq
  rw [sum_on_block f hf part k hcover _ (fun i hi => by simp [mask, hi])]
  simp [mask, hin]

private theorem masked_form {ι β α : Type} [Fintype ι] [Fintype β] [DecidableEq α]
    (f : β → ι) (hf : Function.Injective f) (part : ι → α) (k : α)
    (hin : ∀ j, part (f j) = k) (hcover : ∀ i, part i = k → ∃ j, f j = i)
    (A : ι → ι → ℚ) (x : ι → ℝ) :
    form A (mask part k x) = form (fun i j => A (f i) (f j)) (x ∘ f) := by
  unfold form
  rw [sum_on_block f hf part k hcover _ (fun i hi => by simp [mask, hi])]
  apply Finset.sum_congr rfl
  intro i _
  rw [sum_on_block f hf part k hcover _ (fun j hj => by simp [mask, hj])]
  simp [mask, hin]

variable (d : Input n c m) (modes : Fin m → List (OrbitalEntry n)) (N : ℕ)
  (blocks : Fin b → ShellBlock n) (part : State n → Option (Fin b)) (l u : ℚ)

/-- Data checked once per sector, before replaying its trial energies. -/
structure ShellSetup : Prop where
  valid : Valid d
  modes_eq : ∀ j, modes j = modeEntries d j
  ordered : l ≤ u
  indices : ∀ k, (blocks k).indexCheck N part k
  matrices : ∀ k, (blocks k).matrixCheck (sectorColumn d modes N u)
  rows : ∀ j, shellRowCheck (sectorColumn d modes N u) N blocks part l u j

variable {d modes N blocks part l u}

private theorem ShellSetup.fiber (h : ShellSetup d modes N blocks part l u)
    (k : Fin b) (j : State n) (hj : part j = some k) :
    ∃ i, (blocks k).state i = j := by
  have hr := h.rows j
  rw [shellRowCheck, hj] at hr
  exact hr.1

private theorem ShellSetup.eq_matrix (h : ShellSetup d modes N blocks part l u)
    (k : Fin b) :
    (blocks k).matrix = fun i j => sectorMatrix d N u ((blocks k).state i) ((blocks k).state j) := by
  funext i j
  exact (h.matrices k i j).trans (sectorColumn_entry d modes h.modes_eq N u _ _)

private theorem ShellSetup.off (h : ShellSetup d modes N blocks part l u)
    (i j : State n) (hij : part i ≠ part j) : sectorMatrix d N u i j = 0 := by
  have zero (a t : State n) (k : Fin b) (hk : part t = some k) (hne : part a ≠ part t) :
      sectorMatrix d N u a t = 0 := by
    rw [← sectorColumn_entry d modes h.modes_eq]
    have hh := h.rows t
    rw [shellRowCheck, hk] at hh
    apply off_block _ part _ _ _ hne
    simpa only [hk] using hh.2.1
  cases hj : part j with
  | some k => exact zero i j k hj hij
  | none =>
    cases hi : part i with
    | none => exact (hij (hi.trans hj.symm)).elim
    | some k => rw [sectorMatrix_symmetric d h.valid]; exact zero j i k hi (Ne.symm hij)

theorem ShellSetup.initialLower (h : ShellSetup d modes N blocks part l u)
    (x : State n → ℝ) (hx : supported N x) : (l : ℝ) * normSq x ≤ form (instantaneous d) x := by
  rw [← sectorMatrix_form d N u x hx]
  apply lower_form _ (sectorColumn d modes N u) (fun _ => 1) l
    (sectorColumn_entry d modes h.modes_eq N u) (sectorMatrix_symmetric d h.valid N u)
  intro i
  have hr := h.rows i
  unfold shellRowCheck at hr
  cases hi : part i with
  | some k => rw [hi] at hr; exact hr.2.2
  | none =>
    cases hn : inSector N i with
    | true => exact rowTest_mono _ _ h.ordered (by simpa only [hi, hn, ite_true] using hr)
    | false =>
      simpa [sectorColumn, hn, rowTest, offDiagonal] using h.ordered

private theorem ShellSetup.tailLower (h : ShellSetup d modes N blocks part l u)
    (x : State n → ℝ) :
    (u : ℝ) * normSq (mask part none x) ≤ form (sectorMatrix d N u) (mask part none x) := by
  let cols j := if part j = none then sectorColumn d modes N u j else [(j,u)]
  let A i j := if part i = none ∧ part j = none then sectorMatrix d N u i j
    else if i = j then u else 0
  have he (i j : State n) : entry (cols j) i = A i j := by
    by_cases hi : part i = none <;> by_cases hj : part j = none
    · simp [cols, A, hi, hj, sectorColumn_entry d modes h.modes_eq]
    · have hn : i ≠ j := fun e => hj (e ▸ hi)
      simp [cols, A, hj, hn]
    · have hn : i ≠ j := fun e => hi (e ▸ hj)
      simp [cols, A, hi, hj, hn, sectorColumn_entry d modes h.modes_eq, h.off i j (hj ▸ hi)]
    · simp [cols, A, hj]
  have hsym (i j : State n) : A i j = A j i := by
    simp [A, and_comm, eq_comm (a := i), sectorMatrix_symmetric d h.valid N u i j]
  have hr (i : State n) : rowTest (cols i) (fun _ => 1) u i := by
    by_cases hi : part i = none
    · cases hn : inSector N i
      · simp [cols, hi, hn, sectorColumn, rowTest, offDiagonal]
      · simpa only [cols, hi, ite_true] using
          (show rowTest (sectorColumn d modes N u i) (fun _ => 1) u i from
            by simpa only [shellRowCheck, hi, hn, ite_true] using h.rows i)
    · simp [cols, hi, rowTest, offDiagonal]
  have heq : form A (mask part none x) = form (sectorMatrix d N u) (mask part none x) := by
    unfold form
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hi : part i = none <;> by_cases hj : part j = none <;>
      simp [A, mask, hi, hj]
  rw [← heq]
  exact lower_form A cols _ u he hsym hr _

theorem ShellSetup.lower (h : ShellSetup d modes N blocks part l u)
    {e : ℚ} (heu : e ≤ u)
    (bound : ∀ k x, (e : ℝ) * normSq x ≤ form (blocks k).matrix x)
    (x : State n → ℝ) (hx : supported N x) :
    (e : ℝ) * normSq x ≤ form (instantaneous d) x := by
  rw [← sectorMatrix_form d N u x hx]
  apply partition_lower _ part h.off
  intro k
  cases k with
  | none =>
    exact (mul_le_mul_of_nonneg_right (by exact_mod_cast heu) (normSq_nonneg _)).trans
      (h.tailLower x)
  | some k =>
    have hin := fun i => ((h.indices k).2 i).2
    have hc := h.fiber k
    rw [masked_norm _ (h.indices k).1 _ _ hin hc, masked_form _ (h.indices k).1 _ _ hin hc]
    rw [← h.eq_matrix k]
    exact bound k _

def SectorUpper (d : Input n c m) (N : ℕ) (e : ℚ) : Prop :=
  ∃ x : State n → ℝ, supported N x ∧ 0 < normSq x ∧
    form (instantaneous d) x ≤ (e : ℝ) * normSq x

theorem ShellSetup.upper (h : ShellSetup d modes N blocks part l u)
    (k : Fin b) (e : ℚ) (v : Fin (blocks k).p ⊕ Fin (blocks k).q → ℝ)
    (hv : 0 < normSq v) (hu : form (blocks k).matrix v ≤ (e : ℝ) * normSq v) :
    SectorUpper d N e := by
  classical
  let f := (blocks k).state
  let x (i : State n) := if hi : ∃ j, f j = i then v hi.choose else 0
  have he : x ∘ f = v := by
    funext i
    have hi : ∃ j, f j = f i := ⟨i, rfl⟩
    simp only [Function.comp_apply, x, dite_eq_left hi]
    rw [(h.indices k).1 hi.choose_spec]
  have hx : supported N x := by
    intro i hi
    have hn : ¬ ∃ j, f j = i := by
      rintro ⟨j, rfl⟩
      have hj := ((h.indices k).2 j).1
      change inSector N (f j) = true at hj
      simp [hi] at hj
    simp only [x, dite_eq_right hn]
  have hm : mask part (some k) x = x := by
    funext i
    by_cases hi : part i = some k
    · simp [mask, hi]
    · have hn : ¬ ∃ j, f j = i := by
        rintro ⟨j, rfl⟩
        exact hi ((h.indices k).2 j).2
      simp only [mask, hi, ite_false, x, dite_eq_right hn]
  have hin := fun i => ((h.indices k).2 i).2
  have hc := h.fiber k
  have hn := masked_norm f (h.indices k).1 part (some k) hin hc x
  have hf := masked_form f (h.indices k).1 part (some k) hin hc (sectorMatrix d N u) x
  rw [hm, he] at hn hf
  change form (sectorMatrix d N u) x =
    form (fun i j => sectorMatrix d N u ((blocks k).state i) ((blocks k).state j)) v at hf
  rw [← h.eq_matrix k] at hf
  refine ⟨x, hx, hn.symm ▸ hv, ?_⟩
  rw [← sectorMatrix_form d N u x hx, hf, hn]
  exact hu

/-- Preserve a variational lower bound and an explicit upper trial across bracket updates. -/
structure SectorBracket (d : Input n c m) (N : ℕ) (l u : ℚ) : Prop where
  lower : ∀ x, supported N x → (l : ℝ) * normSq x ≤ form (instantaneous d) x
  upper : SectorUpper d N u

theorem SectorBracket.bounds (h : SectorBracket d N l u) :
    (l : ℝ) ≤ electronicGround d N ∧ electronicGround d N ≤ (u : ℝ) := by
  obtain ⟨x, hx, hn, hu⟩ := h.upper
  exact electronic_bounds d N h.lower x hx hn hu

theorem SectorBracket.updateLower (h : SectorBracket d N l u) {a : ℚ}
    (_midpoint : a = (l + u) / 2)
    (hl : ∀ x, supported N x → (a : ℝ) * normSq x ≤ form (instantaneous d) x) :
    SectorBracket d N a u := ⟨hl, h.upper⟩

theorem SectorBracket.updateUpper (h : SectorBracket d N l u) {a : ℚ}
    (_midpoint : a = (l + u) / 2)
    (hu : SectorUpper d N a) : SectorBracket d N l a := ⟨h.lower, hu⟩

theorem SectorBracket.intersect (h : SectorBracket d N l u) (z ε : ℚ)
    (_midpoint : z = (l + u) / 2)
    (hl : ∀ x, supported N x → ((z - ε : ℚ) : ℝ) * normSq x ≤ form (instantaneous d) x)
    (hu : SectorUpper d N (z + ε)) :
    SectorBracket d N (max l (z - ε)) (min u (z + ε)) := by
  constructor
  · intro x hx
    rw [Rat.cast_max, max_mul_of_nonneg _ _ (normSq_nonneg _)]
    exact max_le (h.lower x hx) (hl x hx)
  · rcases le_total u (z + ε) with he | he
    · simpa only [min_eq_left he] using h.upper
    · simpa only [min_eq_right he] using hu


/-- The predictor keeps all orbitals tied at the active-shell cutoff. -/
def retainedState (d : Input n c m) (N active : ℕ) (i : State n) : Bool :=
  if N = 0 ∨ N = 2*n then true else
    let levels := (List.finRange n).map d.levels
    let mu := (levels[(N-1)/2]?.getD 0 + levels[N/2]?.getD 0) / 2
    let distances := (levels.map fun e => |e - mu|).insertionSort (· ≤ ·)
    let cutoff := distances[active-1]?.getD 0
    (List.finRange n).all fun j =>
      if d.levels j < mu - cutoff then occupied i (j, 0) && occupied i (j, 1)
      else if d.levels j > mu + cutoff then !occupied i (j, 0) && !occupied i (j, 1)
      else true

def ShellBlock.retainedCheck (v : ShellBlock n) (d : Input n c m) (N active : ℕ) : Prop :=
  (∀ j, retainedState d N active (v.kept j) = true) ∧
  (∀ j, retainedState d N active (v.discarded j) = false)

instance (v : ShellBlock n) (d : Input n c m) (N active : ℕ) :
    Decidable (v.retainedCheck d N active) := by unfold ShellBlock.retainedCheck; infer_instance

def ShellBlock.reductionCheck (v : ShellBlock n) (z δ ε : ℚ) (W : Fin v.q → Fin v.p → ℚ) : Prop :=
  let D := shift v.D z
  0 < δ ∧ 0 ≤ ε ∧
    (∀ i, δ + (∑ j, if j = i then 0 else |D i j|) ≤ D i i) ∧
    (∑ i, ∑ j, residual v.B D W i j ^ 2) ≤ δ * ε

instance (v : ShellBlock n) (z δ ε : ℚ) (W : Fin v.q → Fin v.p → ℚ) :
    Decidable (v.reductionCheck z δ ε W) := by unfold ShellBlock.reductionCheck; infer_instance

def ShellBlock.gramCheck (v : ShellBlock n) (z s : ℚ) (W : Fin v.q → Fin v.p → ℚ)
    (L : Fin v.p → Fin v.p → ℚ) (diag : Fin v.p → ℚ) : Prop :=
  (∀ k, 0 ≤ diag k) ∧
  ∀ i j, shift (v.liftedAt z W) s i j = ∑ k, L i k * diag k * L j k

instance (v : ShellBlock n) (z s : ℚ) (W : Fin v.q → Fin v.p → ℚ)
    (L : Fin v.p → Fin v.p → ℚ) (diag : Fin v.p → ℚ) :
    Decidable (v.gramCheck z s W L diag) := by unfold ShellBlock.gramCheck; infer_instance

theorem ShellBlock.reductionCheck_mono {v : ShellBlock n} {z δ ε ε' : ℚ}
    {W : Fin v.q → Fin v.p → ℚ} (h : v.reductionCheck z δ ε W) (he : ε ≤ ε') :
    v.reductionCheck z δ ε' W :=
  ⟨h.1, h.2.1.trans he, h.2.2.1, h.2.2.2.trans (mul_le_mul_of_nonneg_left he h.1.le)⟩

def ShellBlock.trialVector (v : ShellBlock n) (W : Fin v.q → Fin v.p → ℚ)
    (trial : Fin v.p → ℚ) : Vector (State n) :=
  ((List.finRange v.p).map fun i => (v.kept i, trial i)) ++
    ((List.finRange v.q).map fun i => (v.discarded i, ∑ j, W i j * trial j))

def ShellBlock.upperCheck (v : ShellBlock n) (z s : ℚ) (W : Fin v.q → Fin v.p → ℚ)
    (trial : Fin v.p → ℚ) : Prop :=
  0 < rationalNormSq trial ∧ rayleighNumerator (v.liftedAt z W) trial ≤ s * rationalNormSq trial

instance (v : ShellBlock n) (z s : ℚ) (W : Fin v.q → Fin v.p → ℚ) (trial : Fin v.p → ℚ) :
    Decidable (v.upperCheck z s W trial) := by unfold ShellBlock.upperCheck; infer_instance

def ShellBlock.rowBound (v : ShellBlock n) (e : ℚ) : Prop :=
  ∀ i, e + (∑ j, if j = i then 0 else |v.matrix i j|) ≤ v.matrix i i

instance (v : ShellBlock n) (e : ℚ) : Decidable (v.rowBound e) := by
  unfold ShellBlock.rowBound
  infer_instance

private theorem ShellBlock.shift_matrix (v : ShellBlock n) (z : ℚ) :
    shift v.matrix z = shellMatrix (shift v.A z) v.B (shift v.D z) := by
  funext i j
  cases i <;> cases j <;> simp [shift, ShellBlock.matrix, shellMatrix]

theorem ShellSetup.blockRowLower (h : ShellSetup d modes N blocks part l u)
    (k : Fin b) (e : ℚ) (hr : (blocks k).rowBound e) (x : Fin (blocks k).p ⊕ Fin (blocks k).q → ℝ) :
    (e : ℝ) * normSq x ≤ form (blocks k).matrix x :=
  pivot_lower _ (fun i j => by rw [h.eq_matrix]; exact sectorMatrix_symmetric d h.valid N u _ _) e hr x

theorem ShellSetup.blockStepLower (h : ShellSetup d modes N blocks part l u)
    (k : Fin b) (z e δ ε : ℚ) (W : Fin (blocks k).q → Fin (blocks k).p → ℚ)
    (L : Fin (blocks k).p → Fin (blocks k).p → ℚ) (diag : Fin (blocks k).p → ℚ)
    (he : e ≤ z) (hr : (blocks k).reductionCheck z δ ε W)
    (hg : (blocks k).gramCheck z (ε - (z - e)) W L diag)
    (x : Fin (blocks k).p ⊕ Fin (blocks k).q → ℝ) :
    (e : ℝ) * normSq x ≤ form (blocks k).matrix x := by
  let v := blocks k
  have hD (i j : Fin v.q) : shift v.D z i j = shift v.D z j i := by
    have hsym : v.D i j = v.D j i := by
      change v.matrix (.inr i) (.inr j) = v.matrix (.inr j) (.inr i)
      simp only [v, h.eq_matrix]
      exact sectorMatrix_symmetric d h.valid N u _ _
    simp [shift, hsym, eq_comm (a := i)]
  have hl := shell_lower (shift v.A z) v.B (shift v.D z) W δ ε (z - e)
    hD hr.1 (sub_nonneg.mpr he) hr.2.2.1 hr.2.2.2
    (gram_lower L diag (v.liftedAt z W) _ hg.1 hg.2) x
  rw [← v.shift_matrix, form_shift] at hl
  push_cast at hl
  linarith

theorem ShellSetup.blockStepUpper (h : ShellSetup d modes N blocks part l u)
    (k : Fin b) (z e δ ε : ℚ) (W : Fin (blocks k).q → Fin (blocks k).p → ℚ)
    (trial : Fin (blocks k).p → ℚ) (he : z ≤ e)
    (_hr : (blocks k).reductionCheck z δ ε W)
    (ht : (blocks k).upperCheck z (e-z) W trial) : SectorUpper d N e := by
  let v := blocks k
  let x (i : Fin v.p ⊕ Fin v.q) : ℝ :=
    (Sum.elim trial (fun j => ∑ a, W j a * trial a) i : ℚ)
  obtain ⟨hn, hu⟩ := shell_upper (shift v.A z) v.B (shift v.D z) W (e-z)
    (sub_nonneg.mpr he) trial ht.1 ht.2
  change 0 < normSq x at hn
  change form (shellMatrix (shift v.A z) v.B (shift v.D z)) x ≤ ((e-z : ℚ) : ℝ) * normSq x at hu
  rw [← v.shift_matrix, form_shift] at hu
  push_cast at hu
  exact h.upper k e x hn (by linarith)

end Grain.HarmonicBand
