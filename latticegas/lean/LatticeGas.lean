import Mathlib

/-!
An exact finite, canonical lattice gas. A proposal chooses one of the 3L³
positive-direction bonds uniformly. Metropolis acceptance is a power of a
rational q; no transcendental evaluation is part of this kernel.
-/
namespace LatticeGas

abbrev Site (L : ℕ) := Fin L × Fin L × Fin L
abbrev Bond (L : ℕ) := Site L × Fin 3
abbrev Config (L : ℕ) := Site L → Bool

def particleCount {L : ℕ} (s : Config L) : ℕ :=
  ∑ x : Site L, (s x).toNat

def nextIndex {L : ℕ} (x : Fin L) : Fin L :=
  ⟨(x.val + 1) % L, Nat.mod_lt _ (Nat.zero_lt_of_lt x.isLt)⟩

def shift {L : ℕ} (b : Bond L) : Site L :=
  let (x, y, z) := b.1
  if b.2 = 0 then (nextIndex x, y, z)
  else if b.2 = 1 then (x, nextIndex y, z)
  else (x, y, nextIndex z)

def exchange {L : ℕ} (s : Config L) (a b : Site L) : Config L :=
  s ∘ (Equiv.swap a b)

theorem particleCount_exchange {L : ℕ} (s : Config L) (a b : Site L) :
    particleCount (exchange s a b) = particleCount s := by
  simp only [particleCount, exchange, Function.comp_apply]
  exact Equiv.sum_comp (Equiv.swap a b) (fun x => (s x).toNat)

def contacts {L : ℕ} (s : Config L) : ℕ :=
  ∑ b : Bond L, if s b.1 && s (shift b) then 1 else 0

def energy {L : ℕ} (s : Config L) : ℤ := -(contacts s : ℤ)

def proposed {L : ℕ} (s : Config L) (b : Bond L) : Config L :=
  exchange s b.1 (shift b)

def acceptance {L : ℕ} (q : ℚ) (s : Config L) (b : Bond L) : ℚ :=
  q ^ ((energy (proposed s b) - energy s).toNat)

theorem acceptance_nonneg {L : ℕ} (q : ℚ) (hq : 0 ≤ q)
    (s : Config L) (b : Bond L) : 0 ≤ acceptance q s b := by
  exact pow_nonneg hq _

theorem acceptance_le_one {L : ℕ} (q : ℚ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (s : Config L) (b : Bond L) : acceptance q s b ≤ 1 := by
  exact pow_le_one₀ hq hq1

abbrev State (L N : ℕ) := {s : Config L // particleCount s = N}

theorem finite_state_space (L N : ℕ) : Finite (State L N) := inferInstance

theorem proposed_twice {L : ℕ} (s : Config L) (b : Bond L) :
    proposed (proposed s b) b = s := by
  funext x
  simp [proposed, exchange, Function.comp_apply, Equiv.swap_apply_self]

def move {L N : ℕ} (s : State L N) (b : Bond L) : State L N :=
  ⟨proposed s.val b, by
    simpa only [proposed] using
      (particleCount_exchange s.val b.1 (shift b)).trans s.property⟩

theorem move_preserves_count {L N : ℕ} (s : State L N) (b : Bond L) :
    particleCount (move s b).val = N := (move s b).property

theorem move_involutive {L N : ℕ} (s : State L N) (b : Bond L) :
    move (move s b) b = s := by
  apply Subtype.ext
  exact proposed_twice s.val b

def gibbsWeight {L N : ℕ} (q : ℚ) (s : State L N) : ℚ :=
  q ^ energy s.val

theorem power_balance (q : ℚ) (hq : q ≠ 0) (a b : ℤ) :
    q ^ a * q ^ ((b - a).toNat) = q ^ b * q ^ ((a - b).toNat) := by
  by_cases hab : a ≤ b
  · have hba : (a - b).toNat = 0 := Int.toNat_eq_zero.mpr (by omega)
    have hab' : ((b - a).toNat : ℤ) = b - a := Int.toNat_of_nonneg (by omega)
    simp only [hba, pow_zero, mul_one]
    rw [← zpow_natCast, ← zpow_add₀ hq, hab']
    congr 1
    omega
  · have hab0 : (b - a).toNat = 0 := Int.toNat_eq_zero.mpr (by omega)
    have hba' : ((a - b).toNat : ℤ) = a - b := Int.toNat_of_nonneg (by omega)
    simp only [hab0, pow_zero, mul_one]
    rw [← zpow_natCast, ← zpow_add₀ hq, hba']
    congr 1
    omega

theorem proposal_detailed_balance {L N : ℕ} (q : ℚ) (hq : 0 < q)
    (s : State L N) (b : Bond L) :
    gibbsWeight q s * acceptance q s.val b =
      gibbsWeight q (move s b) * acceptance q (move s b).val b := by
  change q ^ energy s.val *
      q ^ ((energy (move s b).val - energy s.val).toNat) =
    q ^ energy (move s b).val *
      q ^ ((energy (move (move s b) b).val - energy (move s b).val).toNat)
  rw [move_involutive]
  exact power_balance q (ne_of_gt hq) (energy s.val) (energy (move s b).val)

def contribution {L N : ℕ} (q : ℚ) (s t : State L N) (b : Bond L) : ℚ :=
  (if t = move s b then acceptance q s.val b else 0) +
  (if t = s then 1 - acceptance q s.val b else 0)

theorem contribution_detailed_balance {L N : ℕ} (q : ℚ) (hq : 0 < q)
    (s t : State L N) (b : Bond L) :
    gibbsWeight q s * contribution q s t b =
      gibbsWeight q t * contribution q t s b := by
  classical
  by_cases hm : t = move s b
  · subst t
    by_cases hs : move s b = s
    · simp [hs]
    · have hs' : s ≠ move s b := Ne.symm hs
      simpa [contribution, move_involutive, hs, hs'] using
        proposal_detailed_balance q hq s b
  · have hr : s ≠ move t b := by
      intro he
      apply hm
      have := congrArg (fun u => move u b) he
      simpa only [move_involutive] using this.symm
    by_cases hs : t = s
    · subst t
      rfl
    · have hs' : s ≠ t := Ne.symm hs
      simp [contribution, hm, hr, hs, hs']

def kernel {L N : ℕ} (q : ℚ) (s t : State L N) : ℚ :=
  if Fintype.card (Bond L) = 0 then (if t = s then 1 else 0)
  else (∑ b : Bond L, contribution q s t b) / Fintype.card (Bond L)

theorem contribution_nonneg {L N : ℕ} (q : ℚ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (s t : State L N) (b : Bond L) : 0 ≤ contribution q s t b := by
  unfold contribution
  have ha := acceptance_nonneg q hq s.val b
  have hb := acceptance_le_one q hq hq1 s.val b
  split_ifs <;> positivity

theorem kernel_nonneg {L N : ℕ} (q : ℚ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (s t : State L N) : 0 ≤ kernel q s t := by
  classical
  by_cases h : Fintype.card (Bond L) = 0
  · simp only [kernel, if_pos h]
    split_ifs <;> norm_num
  · rw [kernel, if_neg h]
    exact div_nonneg (Finset.sum_nonneg fun b _ => contribution_nonneg q hq hq1 s t b)
      (Nat.cast_nonneg _)

theorem contribution_sum {L N : ℕ} (q : ℚ) (s : State L N) (b : Bond L) :
    ∑ t : State L N, contribution q s t b = 1 := by
  unfold contribution
  rw [Finset.sum_add_distrib]
  simp

theorem kernel_sum {L N : ℕ} (q : ℚ) (s : State L N) :
    ∑ t : State L N, kernel q s t = 1 := by
  classical
  by_cases h : Fintype.card (Bond L) = 0
  · simp [kernel, h]
  · simp only [kernel, if_neg h]
    simp_rw [← Finset.sum_div]
    rw [Finset.sum_comm]
    simp_rw [contribution_sum]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    exact div_self (by exact_mod_cast h)

theorem kernel_detailed_balance {L N : ℕ} (q : ℚ) (hq : 0 < q)
    (s t : State L N) :
    gibbsWeight q s * kernel q s t = gibbsWeight q t * kernel q t s := by
  classical
  by_cases h : Fintype.card (Bond L) = 0
  · by_cases he : s = t
    · subst t; rfl
    · simp [kernel, h, he, Ne.symm he]
  · rw [kernel, if_neg h, kernel, if_neg h]
    calc
      gibbsWeight q s * ((∑ b, contribution q s t b) / Fintype.card (Bond L)) =
          (∑ b, gibbsWeight q s * contribution q s t b) / Fintype.card (Bond L) := by
            rw [← Finset.mul_sum]
            ring
      _ = (∑ b, gibbsWeight q t * contribution q t s b) / Fintype.card (Bond L) := by
            congr 1
            apply Finset.sum_congr rfl
            intro b _
            exact contribution_detailed_balance q hq s t b
      _ = gibbsWeight q t * ((∑ b, contribution q t s b) / Fintype.card (Bond L)) := by
            rw [← Finset.mul_sum]
            ring

theorem gibbs_stationary {L N : ℕ} (q : ℚ) (hq : 0 < q)
    (t : State L N) :
    ∑ s : State L N, gibbsWeight q s * kernel q s t = gibbsWeight q t := by
  calc
    ∑ s : State L N, gibbsWeight q s * kernel q s t =
        ∑ s : State L N, gibbsWeight q t * kernel q t s := by
          apply Finset.sum_congr rfl
          intro s _
          exact kernel_detailed_balance q hq s t
    _ = gibbsWeight q t * (∑ s : State L N, kernel q t s) := by
          rw [Finset.mul_sum]
    _ = gibbsWeight q t := by rw [kernel_sum]; ring

end LatticeGas
