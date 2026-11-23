import Grain.DFPTAssembly

/-! Variational energies in the fixed-number electronic and harmonic models
of a DFPT export. The harmonic infimum ranges over every finite occupation box. -/

namespace Grain.HarmonicBand

open Phonon Sparse
open scoped BigOperators

variable {n c m : ℕ}

def inSector (N : ℕ) (i : State n) : Bool :=
  (List.range (2*n)).countP i.val.testBit == N

def supported (N : ℕ) (x : State n → ℝ) : Prop :=
  ∀ i, inSector N i = false → x i = 0

def sectorColumn (d : Input n c m) (modes : Fin m → List (OrbitalEntry n))
    (N : ℕ) (l : ℚ) (j : State n) : Vector (State n) :=
  if inSector N j then (instantaneousColumnWith d modes j).filter fun t => inSector N t.1
  else [(j,l)]

def sectorMatrix (d : Input n c m) (N : ℕ) (l : ℚ) (i j : State n) : ℚ :=
  if inSector N i && inSector N j then instantaneous d i j else if i = j then l else 0

theorem sectorColumn_entry (d : Input n c m)
    (modes : Fin m → List (OrbitalEntry n)) (hm : ∀ k, modes k = modeEntries d k)
    (N : ℕ) (l : ℚ) (i j : State n) :
    entry (sectorColumn d modes N l j) i = sectorMatrix d N l i j := by
  have hm' : modes = modeEntries d := funext hm
  subst modes
  unfold sectorColumn
  rw [show instantaneousColumnWith d (modeEntries d) = instantaneousColumn d from rfl]
  by_cases hij : i = j <;>
    cases hi : inSector N i <;> cases hj : inSector N j <;>
    simp_all [sectorMatrix, entry_filter]

theorem sectorMatrix_symmetric (d : Input n c m) (h : Valid d) (N : ℕ) (l : ℚ)
    (i j : State n) : sectorMatrix d N l i j = sectorMatrix d N l j i := by
  simp [sectorMatrix, Bool.and_comm, instantaneous_symmetric d h i j, eq_comm (a := i) (b := j)]

theorem sectorMatrix_form (d : Input n c m) (N : ℕ) (l : ℚ) (x : State n → ℝ)
    (hx : supported N x) : form (sectorMatrix d N l) x = form (instantaneous d) x := by
  unfold form
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  cases hi : inSector N i <;> cases hj : inSector N j <;> simp [sectorMatrix, hi, hj, hx i, hx j]

theorem sector_lower (d : Input n c m) (h : Valid d)
    (modes : Fin m → List (OrbitalEntry n)) (hm : ∀ k, modes k = modeEntries d k)
    (N : ℕ) (l : ℚ) (w : State n → ℚ) (squares : List (ℚ × Vector (State n)))
    (hsquares : ∀ t ∈ squares, 0 ≤ t.1)
    (rows : ∀ j, rowTest (subtractSquares (sectorColumn d modes N l) squares j) w l j)
    (x : State n → ℝ) (hx : supported N x) :
    (l : ℝ) * normSq x ≤ form (instantaneous d) x := by
  rw [← sectorMatrix_form d N l x hx]
  exact lower_with_squares _ _ squares w l (sectorColumn_entry d modes hm N l)
    (sectorMatrix_symmetric d h N l) hsquares rows x

noncomputable def electronicEnergies (d : Input n c m) (N : ℕ) : Set ℝ :=
  {e | ∃ x : State n → ℝ, supported N x ∧ 0 < normSq x ∧
    e = form (instantaneous d) x / normSq x}

noncomputable def electronicGround (d : Input n c m) (N : ℕ) : ℝ :=
  sInf (electronicEnergies d N)

noncomputable def harmonicEnergies (d : Input n c m) (N : ℕ) : Set ℝ :=
  ⋃ cutoff : ℕ, {e | ∃ ψ : Quanta m cutoff → State n → ℝ,
    (∀ q, supported N (ψ q)) ∧ 0 < (∑ q, normSq (ψ q)) ∧
    e = harmonicForm d ψ / (∑ q, normSq (ψ q))}

noncomputable def harmonicGround (d : Input n c m) (N : ℕ) : ℝ :=
  sInf (harmonicEnergies d N)

private theorem inf_bounds (S : Set ℝ) (l u : ℝ) (lower : ∀ e ∈ S, l ≤ e)
    (upper : ∃ e ∈ S, e ≤ u) : l ≤ sInf S ∧ sInf S ≤ u := by
  obtain ⟨e, he, hu⟩ := upper
  exact ⟨le_csInf ⟨e, he⟩ lower, (csInf_le ⟨l, lower⟩ he).trans hu⟩

theorem electronic_bounds (d : Input n c m) (N : ℕ) {l u : ℝ}
    (lower : ∀ x, supported N x → l * normSq x ≤ form (instantaneous d) x)
    (x : State n → ℝ) (hx : supported N x) (hn : 0 < normSq x)
    (upper : form (instantaneous d) x ≤ u * normSq x) :
    l ≤ electronicGround d N ∧ electronicGround d N ≤ u := by
  apply inf_bounds
  · rintro e ⟨y, hy, hpos, rfl⟩
    exact (le_div_iff₀ hpos).2 (lower y hy)
  · exact ⟨_, ⟨x, hx, hn, rfl⟩, (div_le_iff₀ hn).2 upper⟩

private def oneQuantum (j : Fin m) : Quanta m 1 :=
  Function.update 0 j 1

private theorem oneQuantum_ne_zero (j : Fin m) : oneQuantum j ≠ 0 := by
  intro h
  have hj := congrFun h j
  simp [oneQuantum] at hj

private theorem oneQuantum_injective : Function.Injective (@oneQuantum m) := by
  intro j k h
  by_contra hne
  have hj := congrFun h j
  simp [oneQuantum, hne] at hj

private noncomputable def trialBox (x : State n → ℝ) (y : Fin m → State n → ℝ)
    (q : Quanta m 1) : State n → ℝ :=
  (if q = 0 then x else 0) + ∑ j, if q = oneQuantum j then y j else 0

private theorem trialBox_zero (x : State n → ℝ) (y : Fin m → State n → ℝ) :
    trialBox x y 0 = x := by
  simp [trialBox, Ne.symm (oneQuantum_ne_zero _)]

private theorem trialBox_one (x : State n → ℝ) (y : Fin m → State n → ℝ) (j : Fin m) :
    trialBox x y (oneQuantum j) = y j := by
  simp [trialBox, oneQuantum_ne_zero, oneQuantum_injective.eq_iff]

private theorem annihilate_trial (x : State n → ℝ) (y : Fin m → State n → ℝ)
    (j : Fin m) (q : Quanta m 1) :
    annihilate j (trialBox x y) q = if q = 0 then y j else 0 := by
  funext i
  by_cases hq : q = 0
  · subst q
    simp [annihilate]
    change trialBox x y (oneQuantum j) i = y j i
    rw [trialBox_one]
  · by_cases hj : (q j).val + 1 < 2
    · have hj0 : q j = 0 := by
        apply Fin.ext
        change (q j).val = 0
        omega
      let p := Function.update q j ⟨(q j).val + 1, hj⟩
      have hp0 : p ≠ 0 := by
        intro hp
        have hl := congrFun hp j
        simp [p, hj0] at hl
      have hpk (k : Fin m) : p ≠ oneQuantum k := by
        intro hp
        by_cases hk : k = j
        · subst k
          apply hq
          funext a
          by_cases ha : a = j
          · simpa [ha] using hj0
          · have z := congrFun hp a
            simpa [p, oneQuantum, ha] using z
        · have z := congrFun hp j
          simp [p, oneQuantum, Ne.symm hk, hj0] at z
      simp [annihilate, hj, hq, trialBox, hp0, hpk, p]
    · simp [annihilate, hj, hq]

private theorem trialBox_sum (F : (State n → ℝ) → ℝ) (hF : F 0 = 0)
    (x : State n → ℝ) (y : Fin m → State n → ℝ) :
    (∑ q, F (trialBox x y q)) = F x + ∑ j, F (y j) := by
  classical
  have hx (q : Quanta m 1) : F (trialBox x y q) =
      (if q = 0 then F x else 0) + ∑ j, if q = oneQuantum j then F (y j) else 0 := by
    by_cases hq : q = 0
    · subst q
      simp [trialBox_zero, Ne.symm (oneQuantum_ne_zero _)]
    · by_cases h : ∃ j, q = oneQuantum j
      · obtain ⟨j, rfl⟩ := h
        simp [trialBox_one, oneQuantum_ne_zero, oneQuantum_injective.eq_iff]
      · push Not at h
        simp [trialBox, hq, h, hF]
  simp_rw [hx]
  rw [Finset.sum_add_distrib, Finset.sum_comm (s := (Finset.univ : Finset (Quanta m 1))) (t := (Finset.univ : Finset (Fin m)))]
  simp

private theorem harmonic_trial (d : Input n c m) (x : State n → ℝ) (y : Fin m → State n → ℝ) :
    harmonicForm d (trialBox x y) =
      form (electronic d) x + ∑ j, (form (electronic d) (y j) +
        (frequency d j * normSq (y j) +
          2 * coupling d j * inner (y j) (act (electronPhonon d j) x))) := by
  unfold harmonicForm
  rw [Finset.sum_add_distrib, trialBox_sum _ (by simp [form]), Finset.sum_comm (s := (Finset.univ : Finset (Quanta m 1))) (t := (Finset.univ : Finset (Fin m)))]
  rw [add_assoc]
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  have h (q : Quanta m 1) :
      frequency d j * normSq (annihilate j (trialBox x y) q) +
        2 * coupling d j * inner (annihilate j (trialBox x y) q)
          (act (electronPhonon d j) (trialBox x y q)) =
        if q = 0 then frequency d j * normSq (y j) +
          2 * coupling d j * inner (y j) (act (electronPhonon d j) x) else 0 := by
    rw [annihilate_trial]
    by_cases hq : q = 0
    · subst q; simp [trialBox_zero]
    · simp [hq, normSq_zero, Phonon.inner]
  simp_rw [h]
  simp

theorem harmonic_bounds (d : Input n c m) (hd : Valid d) (N : ℕ) {l u ε : ℝ}
    (lower : ∀ x, supported N x → l * normSq x ≤ form (instantaneous d) x)
    (x : State n → ℝ) (hx : supported N x) (hn : 0 < normSq x)
    (upper : form (instantaneous d) x ≤ u * normSq x) (he : 0 ≤ ε)
    (ha : ∀ j, supported N (act (electronPhonon d j) x))
    (cost : let A := fun j => act (electronPhonon d j)
      let y j := dressing A (coupling d j / frequency d j) x j
      (∑ j, (form (electronic d) (y j) - u * normSq (y j))) ≤ ε * normSq x) :
    l ≤ harmonicGround d N ∧ harmonicGround d N ≤ u + ε := by
  apply inf_bounds
  · intro e h
    obtain ⟨cutoff, hc⟩ := Set.mem_iUnion.mp h
    obtain ⟨ψ, hs, hp, rfl⟩ := hc
    apply (le_div_iff₀ hp).2
    rw [Finset.mul_sum]
    exact (Finset.sum_le_sum fun q _ => lower (ψ q) (hs q)).trans (harmonic_lower d hd ψ)
  · let A := fun j => act (electronPhonon d j)
    let y j := dressing A (coupling d j / frequency d j) x j
    have hsupport (q : Quanta m 1) : supported N (trialBox x y q) := by
      intro i hi
      have hy (j : Fin m) : y j i = 0 := by simp [y, dressing, A, ha j i hi]
      simp [trialBox, Pi.add_apply, Finset.sum_apply,
        apply_ite (fun f : State n → ℝ => f i), hx i hi, hy]
    have hpos : 0 < ∑ q, normSq (trialBox x y q) := by
      rw [trialBox_sum normSq normSq_zero]
      exact add_pos_of_pos_of_nonneg hn (Finset.sum_nonneg fun _ _ => normSq_nonneg _)
    refine ⟨_, Set.mem_iUnion.mpr ⟨1, trialBox x y, hsupport, hpos, rfl⟩, (div_le_iff₀ hpos).2 ?_⟩
    rw [harmonic_trial, trialBox_sum normSq normSq_zero]
    have hw (j : Fin m) : 0 < frequency d j := frequency_pos d hd j
    have hcoupling (j : Fin m) : 2 * frequency d j * (coupling d j / frequency d j) = 2 * coupling d j := by
      field_simp [(hw j).ne']
    have hu : form (electronic d) x -
        (∑ j, frequency d j * (coupling d j / frequency d j)^2 * normSq (A j x)) ≤ u * normSq x := by
      rw [instantaneous_form] at upper
      simp_rw [displacement_coefficient d hd]
      simpa [A, div_eq_mul_inv, mul_comm] using upper
    have h := EFT.mode_dressed_upper (form (electronic d)) A (frequency d)
      (fun j => coupling d j / frequency d j) x he hu cost
    simpa only [hcoupling, y, A, ← add_assoc] using h

end Grain.HarmonicBand
