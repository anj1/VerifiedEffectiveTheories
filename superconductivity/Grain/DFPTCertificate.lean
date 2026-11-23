import Grain.DFPTSector

/-! Exact rational tests for the two-sided DFPT sector enclosures. -/

namespace Grain.HarmonicBand

open Phonon Sparse
open scoped BigOperators

variable {n c m : ℕ}

def defaultWeight : ℚ := 10^26

def lookupWeight (table : Array (State n × ℚ)) (i : State n) : ℚ :=
  ((table.binSearch (i, 0) (fun a b => a.1 < b.1)).map Prod.snd).getD defaultWeight

structure SectorWitness (n : ℕ) where
  lower : ℚ
  electronicUpper : ℚ
  trialUpper : ℚ
  harmonicUpper : ℚ
  weights : State n → ℚ
  trial : Vector (State n)
  electronicTrial : Option (Vector (State n)) := none
  squares : List (ℚ × Vector (State n)) := []
  rowBudget : Option ℚ := none

def cappedWeight (w : SectorWitness n) (N : ℕ) (j : State n) : ℚ :=
  if inSector N j then min defaultWeight (w.weights j) else defaultWeight

private theorem cappedWeight_le (w : SectorWitness n) (N : ℕ) (j : State n) :
    cappedWeight w N j ≤ defaultWeight := by
  unfold cappedWeight
  split
  · exact min_le_left _ _
  · exact le_rfl

def budgetCheck (d : Input n c m) (modes : Fin m → List (OrbitalEntry n))
    (w : SectorWitness n) : Prop :=
  match w.rowBudget with
  | none => True
  | some b => d.density = [] ∧ d.scattering = [] ∧ w.squares = [] ∧
    perturbationAllowance d modes ≤ b

instance (d : Input n c m) (modes : Fin m → List (OrbitalEntry n))
    (w : SectorWitness n) : Decidable (budgetCheck d modes w) := by
  unfold budgetCheck
  split <;> infer_instance

def rowCheck (d : Input n c m) (modes : Fin m → List (OrbitalEntry n))
    (N : ℕ) (w : SectorWitness n) (i : State n) : Prop :=
  if inSector N i = false ∧ w.squares = [] then True
  else if w.rowBudget.isSome ∧ inSector N i = true ∧ cappedWeight w N i = defaultWeight ∧
      w.lower + w.rowBudget.getD 0 ≤ kineticValue d i then True
  else rowTest (subtractSquares (sectorColumn d modes N w.lower) w.squares i)
    (cappedWeight w N) w.lower i

instance (d : Input n c m) (modes : Fin m → List (OrbitalEntry n))
    (N : ℕ) (w : SectorWitness n) (i : State n) : Decidable (rowCheck d modes N w i) := by
  unfold rowCheck
  infer_instance

theorem all_rows_of_chunks {chunks n : ℕ} (hsize : 2^(2*n) = chunks*64)
    (P : State n → Prop)
    (h : ∀ i : Fin chunks, ∀ j : Fin 64, P (Fin.ofNat _ (64*i.val + j.val))) :
    ∀ i, P i := by
  intro i
  have hi : i.val / 64 < chunks := by
    apply (Nat.div_lt_iff_lt_mul (by decide)).2
    rw [← hsize]
    exact i.isLt
  have he : Fin.ofNat (2^(2*n)) (64*(i.val / 64) + i.val % 64) = i := by
    rw [Nat.div_add_mod]
    exact Fin.ext (Nat.mod_eq_of_lt i.isLt)
  rw [← he]
  exact h ⟨i.val / 64, hi⟩ ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩

def frequencyTest (d : Input n c m) (ω : Fin m → ℚ) : Prop :=
  ∀ j, 0 < ω j ∧ ω j ^ 2 ≤ d.force j

instance (d : Input n c m) (ω : Fin m → ℚ) : Decidable (frequencyTest d ω) := by
  unfold frequencyTest
  infer_instance

private def vectorTest (N : ℕ) (v : Vector (State n)) : Bool :=
  v.all fun t => inSector N t.1

private def dressedVector (modes : Fin m → List (OrbitalEntry n))
    (v : Vector (State n)) (j : Fin m) : Vector (State n) :=
  compact (Sparse.apply (modeColumns (modes j)) v)

private def modeCost (d : Input n c m) (modes : Fin m → List (OrbitalEntry n))
    (ω : Fin m → ℚ) (w : SectorWitness n) (j : Fin m) : ℚ :=
  let v := dressedVector modes w.trial j
  max 0 (quadratic (electronicColumn d) v - w.trialUpper * dot v (entry v)) /
    (2 * d.force j * ω j)

/-- A sparse rational vector checked against the assembled electronic operator. -/
def electronicTrialCheck (d : Input n c m) (modes : Fin m → List (OrbitalEntry n))
    (N : ℕ) (u : ℚ) (v : Vector (State n)) : Prop :=
  vectorTest N v = true ∧ 0 < dot v (entry v) ∧
    quadratic (instantaneousColumnWith d modes) v ≤ u * dot v (entry v)

instance (d : Input n c m) (modes : Fin m → List (OrbitalEntry n))
    (N : ℕ) (u : ℚ) (v : Vector (State n)) : Decidable (electronicTrialCheck d modes N u v) := by
  unfold electronicTrialCheck
  infer_instance

def harmonicTrialCheck (d : Input n c m) (modes : Fin m → List (OrbitalEntry n))
    (ω : Fin m → ℚ) (N : ℕ) (w : SectorWitness n) : Prop :=
  electronicTrialCheck d modes N w.trialUpper w.trial ∧
    (∀ j, vectorTest N (dressedVector modes w.trial j) = true) ∧
    w.trialUpper ≤ w.harmonicUpper ∧
    ((List.finRange m).map (modeCost d modes ω w)).sum ≤
      (w.harmonicUpper - w.trialUpper) * dot w.trial (entry w.trial)

instance (d : Input n c m) (modes : Fin m → List (OrbitalEntry n))
    (ω : Fin m → ℚ) (N : ℕ) (w : SectorWitness n) : Decidable (harmonicTrialCheck d modes ω N w) := by
  unfold harmonicTrialCheck
  infer_instance

def trialCheck (d : Input n c m) (modes : Fin m → List (OrbitalEntry n))
    (ω : Fin m → ℚ) (N : ℕ) (w : SectorWitness n) : Prop :=
  harmonicTrialCheck d modes ω N w ∧
    electronicTrialCheck d modes N w.electronicUpper (w.electronicTrial.getD w.trial) ∧
    (w.squares.all fun t => decide (0 ≤ t.1)) = true ∧ budgetCheck d modes w

instance (d : Input n c m) (modes : Fin m → List (OrbitalEntry n))
    (ω : Fin m → ℚ) (N : ℕ) (w : SectorWitness n) : Decidable (trialCheck d modes ω N w) := by
  unfold trialCheck
  infer_instance

private theorem vector_supported {v : Vector (State n)} {N : ℕ}
    (h : vectorTest N v = true) : supported N (fun i => (entry v i : ℝ)) := by
  intro i hi
  have hz : entry v i = 0 := by
    have hf : v.filter (fun t => inSector N t.1) = v :=
      List.filter_eq_self.mpr (List.all_eq_true.mp h)
    simpa [hf, hi] using entry_filter v (inSector N) i
  simp [hz]

private theorem quadratic_cast (columns : State n → Vector (State n))
    (A : State n → State n → ℚ) (h : ∀ i j, entry (columns j) i = A i j)
    (v : Vector (State n)) :
    (quadratic columns v : ℝ) = form A (fun i => (entry v i : ℝ)) := by
  simp only [quadratic_eq, h, form_cast]

private theorem norm_cast (v : Vector (State n)) :
    (dot v (entry v) : ℝ) = normSq (fun i => (entry v i : ℝ)) := by
  rw [dot_self, normSq_cast]

private theorem dressed_cast (d : Input n c m) (j : Fin m) (v : Vector (State n)) :
    (fun i => (entry (dressedVector (modeEntries d) v j) i : ℝ)) =
      act (electronPhonon d j) (fun i => (entry v i : ℝ)) := by
  funext i
  unfold dressedVector
  rw [entry_compact, entry_apply]
  change (↑(∑ a, entry (vertexColumns d j a) i * entry v a) : ℝ) = _
  simp [vertexColumns_entry, act]

private theorem dressing_sq (d : Input n c m) (h : Valid d) (j : Fin m) :
    (coupling d j / frequency d j)^2 = 1 / (2 * (d.force j : ℝ) * frequency d j) := by
  have hω := frequency_pos d h j
  have he := displacement_coefficient d h j
  calc
    _ = (frequency d j * (coupling d j / frequency d j)^2) / frequency d j := by
      field_simp
    _ = _ := by rw [he, div_div]

theorem electronic_trial (d : Input n c m) (modes : Fin m → List (OrbitalEntry n))
    (hm : ∀ j, modes j = modeEntries d j) (N : ℕ) (u : ℚ) (v : Vector (State n))
    (h : electronicTrialCheck d modes N u v) :
    ∃ x : State n → ℝ, supported N x ∧ 0 < normSq x ∧
      form (instantaneous d) x ≤ (u : ℝ) * normSq x := by
  have hm' := funext hm
  subst modes
  refine ⟨_, vector_supported h.1, ?_, ?_⟩
  · rw [← norm_cast]
    exact_mod_cast h.2.1
  · rw [← quadratic_cast (instantaneousColumn d) _ (instantaneousColumn_entry d), ← norm_cast]
    exact_mod_cast h.2.2

/-- Dress an electronic trial using a lower bound supplied by either certificate path. -/
theorem harmonic_trial_certificate (d : Input n c m) (h : Valid d)
    (modes : Fin m → List (OrbitalEntry n)) (hm : ∀ j, modes j = modeEntries d j)
    (ω : Fin m → ℚ) (hω : frequencyTest d ω) (N : ℕ) (w : SectorWitness n)
    (lower : ∀ x, supported N x → (w.lower : ℝ) * normSq x ≤ form (instantaneous d) x)
    (ht : harmonicTrialCheck d modes ω N w) :
    (w.lower : ℝ) ≤ harmonicGround d N ∧ harmonicGround d N ≤ (w.harmonicUpper : ℝ) := by
  have hm' : modes = modeEntries d := funext hm
  subst modes
  obtain ⟨⟨hs, hn, hu⟩, ha, he, hc⟩ := ht
  let x : State n → ℝ := fun i => (entry w.trial i : ℝ)
  have hx := vector_supported hs
  have hnorm : 0 < normSq x := by
    dsimp [x]
    rw [← norm_cast]
    exact_mod_cast hn
  have hquad := quadratic_cast (instantaneousColumn d) _ (instantaneousColumn_entry d) w.trial
  have hupper : form (instantaneous d) x ≤ (w.trialUpper : ℝ) * normSq x := by
    dsimp [x]
    rw [← hquad, ← norm_cast]
    exact_mod_cast hu
  have hε : (0 : ℝ) ≤ (w.harmonicUpper : ℝ) - w.trialUpper := by
    exact sub_nonneg.mpr (by exact_mod_cast he)
  have hb := harmonic_bounds d h N lower x hx hnorm hupper hε
    (fun j => by rw [← dressed_cast]; exact vector_supported (ha j))
  suffices cost :
      (∑ j, (form (electronic d) (dressing (fun j => act (electronPhonon d j))
        (coupling d j / frequency d j) x j) - (w.trialUpper : ℝ) *
        normSq (dressing (fun j => act (electronPhonon d j))
          (coupling d j / frequency d j) x j))) ≤
        ((w.harmonicUpper : ℝ) - w.trialUpper) * normSq x by
    obtain ⟨hl, hu⟩ := hb cost
    exact ⟨hl, by linarith⟩
  refine le_trans ?_ ?_ (b := ∑ j, (modeCost d (modeEntries d) ω w j : ℝ))
  · apply Finset.sum_le_sum
    intro j _
    let z := dressedVector (modeEntries d) w.trial j
    let a : ℝ := coupling d j / frequency d j
    have hz : (fun i => (entry z i : ℝ)) = act (electronPhonon d j) x := dressed_cast d j w.trial
    have hquad := quadratic_cast (electronicColumn d) _ (electronicColumn_entry d) z
    have hns := norm_cast z
    change form (electronic d) (fun i => -a * act (electronPhonon d j) x i) -
      (w.trialUpper : ℝ) * normSq (fun i => -a * act (electronPhonon d j) x i) ≤ _
    rw [← hz]
    have h1 : form (electronic d) (fun i => -a * (entry z i : ℝ)) =
        a^2 * form (electronic d) (fun i => (entry z i : ℝ)) := by
      simp only [form, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
    have h2 : normSq (fun i => -a * (entry z i : ℝ)) = a^2 * normSq (fun i => (entry z i : ℝ)) := by
      simp [normSq, mul_pow, Finset.mul_sum]
    rw [h1, h2, ← hquad, ← hns, show a^2 = _ from dressing_sq d h j, mul_left_comm (w.trialUpper : ℝ), ← mul_sub]
    have hωpos : (0 : ℝ) < ω j := by exact_mod_cast (hω j).1
    have hωle : (ω j : ℝ) ≤ frequency d j := by
      apply (Real.le_sqrt (by positivity) (by
        exact_mod_cast (hω j).2.trans' (sq_nonneg (ω j)))).2
      exact_mod_cast (hω j).2
    have hf : (0 : ℝ) < d.force j := by
      have hfq := lt_of_lt_of_le (pow_pos (hω j).1 2) (hω j).2
      exact_mod_cast hfq
    have hden : 0 < 2 * (d.force j : ℝ) * ω j := by positivity
    simp only [modeCost, ← show z = dressedVector (modeEntries d) w.trial j from rfl,
      Rat.cast_div, Rat.cast_max, Rat.cast_zero, Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat]
    rw [one_div_mul_eq_div]
    exact (div_le_div_of_nonneg_right (le_max_right _ _)
      (mul_nonneg (by positivity) (frequency_pos d h j).le)).trans
      (div_le_div_of_nonneg_left (le_max_left _ _) hden
        (mul_le_mul_of_nonneg_left hωle (by positivity)))
  · change (∑ j, (modeCost d (modeEntries d) ω w j : ℝ)) ≤ _ * normSq (fun i => (entry w.trial i : ℝ))
    rw [← Rat.cast_sum, ← norm_cast]
    rw [← Fin.sum_univ_def] at hc
    exact_mod_cast hc

theorem sector_certificate (d : Input n c m) (h : Valid d)
    (modes : Fin m → List (OrbitalEntry n)) (hm : ∀ j, modes j = modeEntries d j)
    (ω : Fin m → ℚ) (hω : frequencyTest d ω) (N : ℕ) (w : SectorWitness n)
    (hr : ∀ i, rowCheck d modes N w i) (ht : trialCheck d modes ω N w) :
    ((w.lower : ℝ) ≤ electronicGround d N ∧ electronicGround d N ≤ (w.electronicUpper : ℝ)) ∧
    ((w.lower : ℝ) ≤ harmonicGround d N ∧ harmonicGround d N ≤ (w.harmonicUpper : ℝ)) := by
  have hm' : modes = modeEntries d := funext hm
  subst modes
  obtain ⟨htrial, hvt, hpos, hbudget⟩ := ht
  have hlo (i : State n) : rowTest
      (subtractSquares (sectorColumn d (modeEntries d) N w.lower) w.squares i)
      (cappedWeight w N) w.lower i := by
    have hi := hr i
    unfold rowCheck at hi
    split at hi
    · rename_i hout
      obtain ⟨hsector, hsquares⟩ := hout
      simp [sectorColumn, hsector, hsquares, subtractSquares, cappedWeight, rowTest, offDiagonal,
        defaultWeight]
    · split at hi
      · rename_i hfast
        obtain ⟨his, hsector, hw, hk⟩ := hfast
        cases hb : w.rowBudget with
        | none => simp [hb] at his
        | some b =>
          rw [hb] at hk
          unfold budgetCheck at hbudget
          rw [hb] at hbudget
          obtain ⟨hd, hscat, hsquares, hbudget⟩ := hbudget
          rw [hsquares]
          simp only [subtractSquares, sectorColumn, hsector, ite_true, instantaneousColumnWith,
            List.filter_cons]
          apply rowTest_kinetic _ _ _ _ b
          · rw [hw]; norm_num [defaultWeight]
          · intro j
            rw [hw]
            exact cappedWeight_le w N j
          · exact (absSum_filter _ _).trans ((absSum_compact _).trans
              ((perturbation_absSum d _ h hd hscat i).trans hbudget))
          · exact hk
      · exact hi
  have lower := sector_lower d h (modeEntries d) (fun _ => rfl) N w.lower (cappedWeight w N) w.squares
    (fun t ht => of_decide_eq_true (List.all_eq_true.mp hpos t ht)) hlo
  obtain ⟨x, hx, hn, hu⟩ := electronic_trial d (modeEntries d) (fun _ => rfl) N _ _ hvt
  exact ⟨electronic_bounds d N lower x hx hn hu,
    harmonic_trial_certificate d h (modeEntries d) (fun _ => rfl) ω hω N w lower htrial⟩

theorem widen_bounds {l u budget : ℚ} {e : ℝ} (h : 0 ≤ budget)
    (b : (l : ℝ) ≤ e ∧ e ≤ (u : ℝ)) :
    ((l - budget : ℚ) : ℝ) ≤ e ∧ e ≤ ((u + budget : ℚ) : ℝ) := by
  push_cast
  have h' : (0 : ℝ) ≤ budget := by exact_mod_cast h
  constructor <;> linarith [b.1, b.2]

theorem certified_contrast {ι : Type} [Fintype ι] (w lo hi : ι → ℚ) (energy : ι → ℝ)
    (bounds : ∀ i, (lo i : ℝ) ≤ energy i ∧ energy i ≤ (hi i : ℝ)) (l u : ℚ)
    (hl : l ≤ ∑ i, min (w i * lo i) (w i * hi i))
    (hu : (∑ i, max (w i * lo i) (w i * hi i)) ≤ u) :
    (l : ℝ) ≤ (∑ i, (w i : ℝ) * energy i) ∧ (∑ i, (w i : ℝ) * energy i) ≤ (u : ℝ) := by
  obtain ⟨hlo, hhi⟩ := EFT.contrast_enclosure (fun i => (w i : ℝ))
    (fun i => (lo i : ℝ)) (fun i => (hi i : ℝ)) energy bounds
  constructor
  · refine le_trans ?_ hlo
    exact_mod_cast hl
  · refine le_trans hhi ?_
    exact_mod_cast hu

end Grain.HarmonicBand
