import GrandCanonical

/-!
Phenomenological-RG foundations for the finite zero-field Ising experiment.
The microscopic heat-bath identification is proved here before using CFTP
outputs for quotients of observables.
-/
namespace GrandCanonical

open LatticeGas


def setSpin {L : ℕ} (s : Spin L) (x : Site L) (v : Bool) : Spin L :=
  fun y => if y = x then v else s y

theorem setSpin_at {L : ℕ} (s : Spin L) (x : Site L) (v : Bool) :
    setSpin s x v x = v := by simp [setSpin]

theorem setSpin_away {L : ℕ} (s : Spin L) (x y : Site L) (v : Bool)
    (h : y ≠ x) : setSpin s x v y = s y := by simp [setSpin, h]

theorem nextIndex_eq_add_one {L : ℕ} (hL : 1 < L) (x : Fin L) :
    nextIndex x = x + (⟨1, hL⟩ : Fin L) := by
  apply Fin.ext
  simp [nextIndex, Fin.val_add]

theorem prevIndex_eq_sub_one {L : ℕ} (hL : 1 < L) (hL0 : 0 < L) (x : Fin L) :
    prevIndex hL0 x = x - (⟨1, hL⟩ : Fin L) := by
  apply Fin.ext
  simp only [prevIndex, Fin.val_sub, Fin.val_mk]
  congr 1
  omega

theorem nextIndex_prevIndex {L : ℕ} (hL : 1 < L) (hL0 : 0 < L) (x : Fin L) :
    nextIndex (prevIndex hL0 x) = x := by
  apply Fin.ext
  simp only [nextIndex, prevIndex]
  by_cases hx : x.val = 0
  · have hprev : (x.val + L - 1) % L = L - 1 := by
      rw [hx]
      simp [Nat.mod_eq_of_lt (by omega : L - 1 < L)]
    rw [hprev]
    have hsum : L - 1 + 1 = L := by omega
    rw [hsum, Nat.mod_self]
    omega
  · have hprev : (x.val + L - 1) % L = x.val - 1 := by
      have heq : x.val + L - 1 = (x.val - 1) + L := by omega
      rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : x.val - 1 < L)]
    rw [hprev]
    have heq : x.val - 1 + 1 = x.val := by omega
    rw [heq, Nat.mod_eq_of_lt x.isLt]

theorem prevIndex_nextIndex {L : ℕ} (hL : 1 < L) (hL0 : 0 < L) (x : Fin L) :
    prevIndex hL0 (nextIndex x) = x := by
  apply Fin.ext
  simp only [nextIndex, prevIndex]
  by_cases hx : x.val + 1 = L
  · have hnext : (x.val + 1) % L = 0 := by rw [hx, Nat.mod_self]
    rw [hnext]
    have hprev : (0 + L - 1) % L = L - 1 := by
      rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega : L - 1 < L)]
    rw [hprev]
    omega
  · have hnext : (x.val + 1) % L = x.val + 1 :=
      Nat.mod_eq_of_lt (by omega)
    rw [hnext]
    have heq : x.val + 1 + L - 1 = x.val + L := by omega
    rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt x.isLt]

def axisPrev {L : ℕ} (hL : 0 < L) (x : Site L) (d : Fin 3) : Site L :=
  if d = 0 then (prevIndex hL x.1, x.2.1, x.2.2)
  else if d = 1 then (x.1, prevIndex hL x.2.1, x.2.2)
  else (x.1, x.2.1, prevIndex hL x.2.2)

theorem shift_axisPrev {L : ℕ} (hL : 1 < L) (hL0 : 0 < L)
    (x : Site L) (d : Fin 3) : shift (axisPrev hL0 x d, d) = x := by
  fin_cases d <;> rcases x with ⟨x,y,z⟩ <;>
    simp [axisPrev, shift, nextIndex_prevIndex hL hL0]

theorem axisPrev_shift {L : ℕ} (hL : 1 < L) (hL0 : 0 < L)
    (y : Site L) (d : Fin 3) : axisPrev hL0 (shift (y,d)) d = y := by
  fin_cases d <;> rcases y with ⟨x,y,z⟩ <;>
    simp [axisPrev, shift, prevIndex_nextIndex hL hL0]

theorem shift_eq_iff {L : ℕ} (hL : 1 < L) (hL0 : 0 < L)
    (x y : Site L) (d : Fin 3) :
    shift (y,d) = x ↔ y = axisPrev hL0 x d := by
  constructor
  · intro h
    calc y = axisPrev hL0 (shift (y,d)) d := (axisPrev_shift hL hL0 y d).symm
      _ = axisPrev hL0 x d := by rw [h]
  · intro h
    rw [h]
    exact shift_axisPrev hL hL0 x d

theorem nextIndex_ne_self {L : ℕ} (hL : 1 < L) (x : Fin L) :
    nextIndex x ≠ x := by
  intro h
  have hv := congrArg Fin.val h
  simp only [nextIndex, Fin.val_mk] at hv
  by_cases hx : x.val + 1 = L
  · rw [hx, Nat.mod_self] at hv
    omega
  · rw [Nat.mod_eq_of_lt (by omega : x.val + 1 < L)] at hv
    omega

theorem shift_ne_source {L : ℕ} (hL : 1 < L) (y : Site L) (d : Fin 3) :
    shift (y,d) ≠ y := by
  fin_cases d <;> rcases y with ⟨x,y,z⟩ <;>
    simp [shift, nextIndex_ne_self hL]

theorem axisPrev_ne_self {L : ℕ} (hL : 1 < L) (hL0 : 0 < L)
    (x : Site L) (d : Fin 3) : axisPrev hL0 x d ≠ x := by
  intro h
  have hs := shift_axisPrev hL hL0 x d
  rw [h] at hs
  exact shift_ne_source hL x d hs

private theorem sum_diff_two {α : Type*} [Fintype α] [DecidableEq α]
    (g h : α → ℤ) (u v : α) (huv : u ≠ v)
    (hag : ∀ y, y ≠ u → y ≠ v → g y = h y) :
    (∑ y, g y) - (∑ y, h y) = (g u - h u) + (g v - h v) := by
  rw [← Finset.sum_sub_distrib]
  have hp (y : α) : g y - h y =
      if y = u then g u - h u else if y = v then g v - h v else 0 := by
    by_cases hyu : y = u
    · subst y; simp
    · by_cases hyv : y = v
      · subst y; simp [huv.symm]
      · simp [hyu, hyv, hag y hyu hyv]
  calc
    (∑ y : α, (g y - h y)) =
        (∑ y : α, (if y = u then g u - h u else
          if y = v then g v - h v else 0)) :=
      Finset.sum_congr rfl (fun y _ => hp y)
    _ = (g u - h u) + (g v - h v) := by
      have hsplit (y : α) :
          (if y = u then g u - h u else if y = v then g v - h v else 0) =
            (if y = u then g u - h u else 0) +
              (if y = v then g v - h v else 0) := by
        by_cases hyu : y = u <;> by_cases hyv : y = v <;>
          simp [hyu, hyv, huv, huv.symm]
      simp_rw [hsplit]
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

def edgeDisagreement {L : ℕ} (s : Spin L) (y : Site L) (d : Fin 3) : ℤ :=
  if s y != s (shift (y,d)) then 1 else 0

theorem disagreeCount_eq_edgeSum {L : ℕ} (s : Spin L) :
    (disagreeCount s : ℤ) = ∑ d : Fin 3, ∑ y : Site L, edgeDisagreement s y d := by
  unfold disagreeCount edgeDisagreement
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]

def spinDelta (b : Bool) : ℤ := if b then -1 else 1

theorem edge_flip_delta {L : ℕ} (hL : 1 < L) (hL0 : 0 < L)
    (s : Spin L) (x : Site L) (d : Fin 3) :
    (∑ y : Site L, edgeDisagreement (setSpin s x true) y d) -
      (∑ y : Site L, edgeDisagreement (setSpin s x false) y d) =
        spinDelta (s (shift (x,d))) + spinDelta (s (axisPrev hL0 x d)) := by
  have haway (y : Site L) (hy : y ≠ x) (hp : y ≠ axisPrev hL0 x d) :
      edgeDisagreement (setSpin s x true) y d =
        edgeDisagreement (setSpin s x false) y d := by
    have ht : shift (y,d) ≠ x := by
      intro he
      exact hp ((shift_eq_iff hL hL0 x y d).mp he)
    simp [edgeDisagreement, setSpin, hy, ht]
  have hsum := sum_diff_two
    (fun y => edgeDisagreement (setSpin s x true) y d)
    (fun y => edgeDisagreement (setSpin s x false) y d)
    x (axisPrev hL0 x d) (axisPrev_ne_self hL hL0 x d).symm haway
  rw [hsum]
  have hshift : shift (x,d) ≠ x := shift_ne_source hL x d
  have hprev : axisPrev hL0 x d ≠ x := axisPrev_ne_self hL hL0 x d
  have hprevshift : shift (axisPrev hL0 x d,d) = x := shift_axisPrev hL hL0 x d
  simp only [edgeDisagreement, setSpin_at, setSpin_away _ _ _ _ hshift,
    setSpin_away _ _ _ _ hprev, hprevshift]
  cases s (shift (x,d)) <;> cases s (axisPrev hL0 x d) <;>
    simp [spinDelta]

theorem plusCount_axis {L : ℕ} (hL0 : 0 < L) (s : Spin L) (x : Site L) :
    plusCount hL0 s x =
      ∑ d : Fin 3, ((s (shift (x,d))).toNat +
        (s (axisPrev hL0 x d)).toNat) := by
  have h0 : neighbour hL0 x (0 : Fin 6) = (nextIndex x.1, x.2.1, x.2.2) := rfl
  have h1 : neighbour hL0 x (1 : Fin 6) = (prevIndex hL0 x.1, x.2.1, x.2.2) := rfl
  have h2 : neighbour hL0 x (2 : Fin 6) = (x.1, nextIndex x.2.1, x.2.2) := rfl
  have h3 : neighbour hL0 x (3 : Fin 6) = (x.1, prevIndex hL0 x.2.1, x.2.2) := rfl
  have h4 : neighbour hL0 x (4 : Fin 6) = (x.1, x.2.1, nextIndex x.2.2) := rfl
  have h5 : neighbour hL0 x (5 : Fin 6) = (x.1, x.2.1, prevIndex hL0 x.2.2) := rfl
  simp [plusCount, Fin.sum_univ_succ, h0, h1, h2, h3, h4, h5, shift, axisPrev]
  rw [add_comm (s (x.1, x.2.1, nextIndex x.2.2)).toNat
    (s (x.1, x.2.1, prevIndex hL0 x.2.2)).toNat]
  simp only [add_assoc]

theorem local_disagreement_difference {L : ℕ} (hL : 1 < L) (hL0 : 0 < L)
    (s : Spin L) (x : Site L) :
    (disagreeCount (setSpin s x true) : ℤ) -
      (disagreeCount (setSpin s x false) : ℤ) =
        6 - 2 * (plusCount hL0 s x : ℤ) := by
  rw [disagreeCount_eq_edgeSum, disagreeCount_eq_edgeSum,
    ← Finset.sum_sub_distrib]
  simp_rw [edge_flip_delta hL hL0 s x]
  have hdelta (b : Bool) : spinDelta b = 1 - 2 * (b.toNat : ℤ) := by
    cases b <;> rfl
  simp_rw [hdelta]
  rw [plusCount_axis]
  simp only [Nat.cast_sum, Nat.cast_add, Fin.sum_univ_succ]
  ring

theorem plusCount_le_six {L : ℕ} (hL0 : 0 < L) (s : Spin L) (x : Site L) :
    plusCount hL0 s x ≤ 6 := by
  unfold plusCount
  calc
    (∑ i : Fin 6, (s (neighbour hL0 x i)).toNat) ≤ ∑ _i : Fin 6, 1 := by
      apply Finset.sum_le_sum
      intro i _
      cases s (neighbour hL0 x i) <;> decide
    _ = 6 := by norm_num

theorem local_disagreement_balance {L : ℕ} (hL : 1 < L) (hL0 : 0 < L)
    (s : Spin L) (x : Site L) :
    disagreeCount (setSpin s x true) + plusCount hL0 s x =
      disagreeCount (setSpin s x false) + (6 - plusCount hL0 s x) := by
  have hdiff := local_disagreement_difference hL hL0 s x
  have ha := plusCount_le_six hL0 s x
  omega

def weightConditional {L : ℕ} (r : ℚ) (s : Spin L) (x : Site L) : ℚ :=
  weight r (setSpin s x true) /
    (weight r (setSpin s x true) + weight r (setSpin s x false))

theorem concrete_heatProb_is_conditional {L : ℕ} (hL : 1 < L) (hL0 : 0 < L)
    (r : ℚ) (hr : 0 < r) (s : Spin L) (x : Site L) :
    weightConditional r s x = heatProb r (plusCount hL0 s x) := by
  have hbal := local_disagreement_balance hL hL0 s x
  have hp : weight r (setSpin s x true) * r ^ (plusCount hL0 s x) =
      weight r (setSpin s x false) * r ^ (6 - plusCount hL0 s x) := by
    unfold weight
    rw [← pow_add, ← pow_add, hbal]
  have hden : weight r (setSpin s x true) + weight r (setSpin s x false) ≠ 0 :=
    ne_of_gt (add_pos (pow_pos hr _) (pow_pos hr _))
  have hden2 : r ^ (6 - plusCount hL0 s x) + r ^ plusCount hL0 s x ≠ 0 :=
    ne_of_gt (add_pos (pow_pos hr _) (pow_pos hr _))
  unfold weightConditional heatProb
  apply (div_eq_div_iff hden hden2).2
  linear_combination hp

theorem setSpin_setSpin {L : ℕ} (s : Spin L) (x : Site L) (v w : Bool) :
    setSpin (setSpin s x v) x w = setSpin s x w := by
  funext y
  by_cases hy : y = x <;> simp [setSpin, hy]

theorem setSpin_self {L : ℕ} (s : Spin L) (x : Site L) :
    setSpin s x (s x) = s := by
  funext y
  by_cases hy : y = x <;> simp [setSpin, hy]

theorem setSpin_reverse {L : ℕ} (s t : Spin L) (x : Site L) (v : Bool)
    (h : s = setSpin t x v) : t = setSpin s x (t x) := by
  funext y
  by_cases hy : y = x
  · subst y
    simp [setSpin]
  · simp [setSpin, hy, h]

def heatKernelSite {L : ℕ} (r : ℚ) (hL0 : 0 < L)
    (x : Site L) (s t : Spin L) : ℚ :=
  (if t = setSpin s x true then heatProb r (plusCount hL0 s x) else 0) +
    (if t = setSpin s x false then 1 - heatProb r (plusCount hL0 s x) else 0)

theorem heatKernelSite_sum {L : ℕ} (r : ℚ) (hL0 : 0 < L)
    (x : Site L) (s : Spin L) : ∑ t : Spin L, heatKernelSite r hL0 x s t = 1 := by
  unfold heatKernelSite
  rw [Finset.sum_add_distrib]
  simp

theorem heatKernelSite_nonneg {L : ℕ} (r : ℚ) (hr : 0 < r)
    (hL0 : 0 < L) (x : Site L) (s t : Spin L) :
    0 ≤ heatKernelSite r hL0 x s t := by
  unfold heatKernelSite
  have hp := heatProb_nonneg r hr (plusCount hL0 s x)
  have hp1 := heatProb_le_one r hr (plusCount hL0 s x)
  split_ifs <;> positivity

theorem weightConditional_balance {L : ℕ} (r : ℚ) (hr : 0 < r)
    (s : Spin L) (x : Site L) :
    weight r (setSpin s x false) * weightConditional r s x =
      weight r (setSpin s x true) * (1 - weightConditional r s x) := by
  have hden : weight r (setSpin s x true) + weight r (setSpin s x false) ≠ 0 :=
    ne_of_gt (add_pos (pow_pos hr _) (pow_pos hr _))
  unfold weightConditional
  field_simp
  ring

theorem heatProb_setSpin {L : ℕ} (hL : 1 < L) (hL0 : 0 < L)
    (r : ℚ) (hr : 0 < r) (s : Spin L) (x : Site L) (v : Bool) :
    heatProb r (plusCount hL0 (setSpin s x v) x) =
      heatProb r (plusCount hL0 s x) := by
  rw [← concrete_heatProb_is_conditional hL hL0 r hr,
    ← concrete_heatProb_is_conditional hL hL0 r hr]
  simp [weightConditional, setSpin_setSpin]

theorem heatKernelSite_balance_pair {L : ℕ} (hL : 1 < L) (hL0 : 0 < L)
    (r : ℚ) (hr : 0 < r) (s : Spin L) (x : Site L) (hsx : s x = false) :
    weight r s * heatKernelSite r hL0 x s (setSpin s x true) =
      weight r (setSpin s x true) * heatKernelSite r hL0 x (setSpin s x true) s := by
  have hminus : setSpin s x false = s := by
    simpa [hsx] using setSpin_self s x
  have hne : setSpin s x true ≠ s := by
    intro he
    have hh := congrArg (fun z : Spin L => z x) he
    simp [setSpin_at, hsx] at hh
  have hne2 : s ≠ setSpin s x true := Ne.symm hne
  have hne3 : setSpin s x true ≠ setSpin s x false := by simpa [hminus] using hne
  have hprob := heatProb_setSpin hL hL0 r hr s x true
  have hbalance := weightConditional_balance r hr s x
  rw [hminus, concrete_heatProb_is_conditional hL hL0 r hr] at hbalance
  have hforward : heatKernelSite r hL0 x s (setSpin s x true) =
      heatProb r (plusCount hL0 s x) := by
    simp [heatKernelSite, hne3]
  have hreverse : heatKernelSite r hL0 x (setSpin s x true) s =
      1 - heatProb r (plusCount hL0 s x) := by
    simp [heatKernelSite, setSpin_setSpin, hminus, hne2, hprob]
  rw [hforward, hreverse]
  exact hbalance

theorem heatKernelSite_detailed_balance {L : ℕ} (hL : 1 < L) (hL0 : 0 < L)
    (r : ℚ) (hr : 0 < r) (x : Site L) (s t : Spin L) :
    weight r s * heatKernelSite r hL0 x s t =
      weight r t * heatKernelSite r hL0 x t s := by
  classical
  by_cases hst : s = t
  · subst t
    rfl
  by_cases htp : t = setSpin s x true
  · subst t
    have hsx : s x = false := by
      cases h : s x
      · rfl
      · have hh : setSpin s x true = s := by simpa [h] using setSpin_self s x
        exact False.elim (hst hh.symm)
    exact heatKernelSite_balance_pair hL hL0 r hr s x hsx
  by_cases htm : t = setSpin s x false
  · subst t
    have hsx : s x = true := by
      cases h : s x
      · have hh : setSpin s x false = s := by simpa [h] using setSpin_self s x
        exact False.elim (hst hh.symm)
      · rfl
    have hplus : setSpin (setSpin s x false) x true = s := by
      rw [setSpin_setSpin]
      simpa [hsx] using setSpin_self s x
    have htx : (setSpin s x false) x = false := setSpin_at s x false
    simpa [hplus] using
      (heatKernelSite_balance_pair hL hL0 r hr (setSpin s x false) x htx).symm
  have hreverse (v : Bool) : s ≠ setSpin t x v := by
    intro hv
    have ht := setSpin_reverse s t x v hv
    cases htx : t x
    · exact htm (by simpa [htx] using ht)
    · exact htp (by simpa [htx] using ht)
  simp [heatKernelSite, htp, htm, hreverse]

theorem heatKernelSite_stationary {L : ℕ} (hL : 1 < L) (hL0 : 0 < L)
    (r : ℚ) (hr : 0 < r) (x : Site L) (t : Spin L) :
    ∑ s : Spin L, equilibrium r s * heatKernelSite r hL0 x s t =
      equilibrium r t := by
  calc
    ∑ s : Spin L, equilibrium r s * heatKernelSite r hL0 x s t =
        ∑ s : Spin L, equilibrium r t * heatKernelSite r hL0 x t s := by
      apply Finset.sum_congr rfl
      intro s _
      unfold equilibrium
      have hdb := heatKernelSite_detailed_balance hL hL0 r hr x s t
      calc
        weight r s / partition r * heatKernelSite r hL0 x s t =
            (weight r s * heatKernelSite r hL0 x s t) / partition r := by ring
        _ = (weight r t * heatKernelSite r hL0 x t s) / partition r := by rw [hdb]
        _ = weight r t / partition r * heatKernelSite r hL0 x t s := by ring
    _ = equilibrium r t * (∑ s : Spin L, heatKernelSite r hL0 x t s) := by
      rw [Finset.mul_sum]
    _ = equilibrium r t := by rw [heatKernelSite_sum]; ring

noncomputable def realExpectation {L : ℕ} (f : Spin L → ℝ) (r : ℝ) : ℝ :=
  realMoment f r / realMoment (L := L) (fun _ => 1) r

noncomputable def realCovariance {L : ℕ} (f g : Spin L → ℝ) (r : ℝ) : ℝ :=
  realExpectation (fun s => f s * g s) r -
    realExpectation f r * realExpectation g r

theorem realMoment_hasDerivAt {L : ℕ} (f : Spin L → ℝ) (r : ℝ) :
    HasDerivAt (realMoment f)
      (∑ s : Spin L, f s * ((disagreeCount s : ℝ) * r ^ (disagreeCount s - 1))) r := by
  unfold realMoment
  apply HasDerivAt.fun_sum
  intro s _
  convert (hasDerivAt_pow (disagreeCount s) r).const_mul (f s) using 1

theorem realMoment_log_derivative {L : ℕ} (f : Spin L → ℝ) (r : ℝ) :
    r * deriv (realMoment f) r =
      realMoment (fun s => f s * (disagreeCount s : ℝ)) r := by
  rw [(realMoment_hasDerivAt f r).deriv]
  unfold realMoment
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hD : disagreeCount s = 0
  · simp [hD]
  · have hpow : r ^ disagreeCount s = r ^ (disagreeCount s - 1) * r := by
      conv_lhs => rw [show disagreeCount s = (disagreeCount s - 1) + 1 by omega]
      simp [pow_succ]
    rw [hpow]
    ring

theorem expectation_log_derivative {L : ℕ} (f : Spin L → ℝ) (r : ℝ)
    (hr : 0 < r) :
    r * deriv (realExpectation f) r =
      realCovariance f (fun s => (disagreeCount s : ℝ)) r := by
  have hZ : realMoment (L := L) (fun _ => 1) r ≠ 0 :=
    ne_of_gt (realMoment_pos (fun _ => 1) r hr (by simp) ⟨fun _ => false, by simp⟩)
  have hdiff := (realMoment_hasDerivAt f r).div
    (realMoment_hasDerivAt (L := L) (fun _ => 1) r) hZ
  have hN := realMoment_log_derivative f r
  have hZD := realMoment_log_derivative (L := L) (fun _ => 1) r
  unfold realCovariance realExpectation
  change r * deriv (realMoment f / realMoment (L := L) (fun _ => 1)) r = _
  rw [hdiff.deriv]
  rw [(realMoment_hasDerivAt f r).deriv] at hN
  rw [(realMoment_hasDerivAt (L := L) (fun _ => 1) r).deriv] at hZD
  simp only [one_mul] at hZD ⊢
  simp only [← mul_assoc] at hN
  field_simp
  linear_combination
    (realMoment (L := L) (fun _ => 1) r) * hN - (realMoment f r) * hZD

noncomputable def binderFromMoments (a b : ℝ) : ℝ := 1 - b / (3 * a ^ 2)

theorem binderFromMoments_derivative
    (a b : ℝ → ℝ) (r a' b' : ℝ)
    (ha : HasDerivAt a a' r) (hb : HasDerivAt b b' r)
    (haval : a r ≠ 0) :
    deriv (fun z => binderFromMoments (a z) (b z)) r =
      -b' / (3 * (a r) ^ 2) + 2 * b r * a' / (3 * (a r) ^ 3) := by
  have hden : 3 * a r ^ 2 ≠ 0 := by positivity
  have hd := (hasDerivAt_const r (1 : ℝ)).sub
    (hb.div ((hasDerivAt_const r (3 : ℝ)).mul (ha.pow 2)) hden)
  change deriv (fun z => (1 : ℝ) - b z / (3 * a z ^ 2)) r = _
  rw [show deriv (fun z => (1 : ℝ) - b z / (3 * a z ^ 2)) r = _ from hd.deriv]
  dsimp
  field_simp
  ring

noncomputable def expectedBinder {L : ℕ} (f₂ f₄ : Spin L → ℝ) (r : ℝ) : ℝ :=
  binderFromMoments (realExpectation f₂ r) (realExpectation f₄ r)

theorem expectedBinder_eq_realBinder {L : ℕ} (f₂ f₄ : Spin L → ℝ)
    (r : ℝ) (hr : 0 < r) (h₂ : realMoment f₂ r ≠ 0) :
    expectedBinder f₂ f₄ r = realBinder f₂ f₄ r := by
  have hZ : realMoment (L := L) (fun _ => 1) r ≠ 0 :=
    ne_of_gt (realMoment_pos (fun _ => 1) r hr (by simp) ⟨fun _ => false, by simp⟩)
  unfold expectedBinder binderFromMoments realExpectation realBinder
  field_simp

theorem expectedBinder_covariance_slope {L : ℕ}
    (f₂ f₄ : Spin L → ℝ) (r : ℝ) (hr : 0 < r)
    (ha : realExpectation f₂ r ≠ 0) :
    r * deriv (expectedBinder f₂ f₄) r =
      -realCovariance f₄ (fun s => (disagreeCount s : ℝ)) r /
        (3 * realExpectation f₂ r ^ 2) +
      2 * realExpectation f₄ r *
        realCovariance f₂ (fun s => (disagreeCount s : ℝ)) r /
        (3 * realExpectation f₂ r ^ 3) := by
  have hZ : realMoment (L := L) (fun _ => 1) r ≠ 0 :=
    ne_of_gt (realMoment_pos (fun _ => 1) r hr (by simp) ⟨fun _ => false, by simp⟩)
  have hda := (realMoment_hasDerivAt f₂ r).div
    (realMoment_hasDerivAt (L := L) (fun _ => 1) r) hZ
  have hdb := (realMoment_hasDerivAt f₄ r).div
    (realMoment_hasDerivAt (L := L) (fun _ => 1) r) hZ
  have hda' : DifferentiableAt ℝ (realExpectation f₂) r := by
    change DifferentiableAt ℝ (realMoment f₂ / realMoment (L := L) (fun _ => 1)) r
    exact hda.differentiableAt
  have hdb' : DifferentiableAt ℝ (realExpectation f₄) r := by
    change DifferentiableAt ℝ (realMoment f₄ / realMoment (L := L) (fun _ => 1)) r
    exact hdb.differentiableAt
  have hs := binderFromMoments_derivative
    (realExpectation f₂) (realExpectation f₄) r
    (deriv (realExpectation f₂) r) (deriv (realExpectation f₄) r)
    hda'.hasDerivAt hdb'.hasDerivAt ha
  have hcov₂ := expectation_log_derivative f₂ r hr
  have hcov₄ := expectation_log_derivative f₄ r hr
  change r * deriv (fun z => binderFromMoments
    (realExpectation f₂ z) (realExpectation f₄ z)) r = _
  rw [hs]
  linear_combination
    (-1 / (3 * realExpectation f₂ r ^ 2)) * hcov₄ +
      (2 * realExpectation f₄ r / (3 * realExpectation f₂ r ^ 3)) * hcov₂

/-- A pilot-chosen center turns the Binder-ratio sign into a confidence
    statement about one bounded observable, retaining the covariance of
    `m²` and `m⁴`. The pilot must be independent of the confirmatory batch. -/
theorem centered_binder_identity (a b c a₀ : ℝ) :
    b - c * a ^ 2 =
      (b - 2 * c * a₀ * a + c * a₀ ^ 2) - c * (a - a₀) ^ 2 := by
  ring

theorem centered_binder_ratio_lt (a b c a₀ gUpper : ℝ)
    (hc : 0 ≤ c)
    (hg : b - 2 * c * a₀ * a + c * a₀ ^ 2 ≤ gUpper)
    (hneg : gUpper < 0) :
    b < c * a ^ 2 := by
  have hid := centered_binder_identity a b c a₀
  nlinarith [sq_nonneg (a - a₀)]

theorem centered_binder_ratio_gt (a b c a₀ gLower e : ℝ)
    (hc : 0 ≤ c) (he : |a - a₀| ≤ e)
    (hg : gLower ≤ b - 2 * c * a₀ * a + c * a₀ ^ 2)
    (hpos : c * e ^ 2 < gLower) :
    c * a ^ 2 < b := by
  have ⟨helo, hehi⟩ := abs_le.mp he
  have he' : (a - a₀) ^ 2 ≤ e ^ 2 := by nlinarith
  have hid := centered_binder_identity a b c a₀
  nlinarith

theorem binder_order_of_ratio_separator (a₁ b₁ a₂ b₂ c : ℝ)
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (h₁ : c * a₁ ^ 2 < b₁) (h₂ : b₂ < c * a₂ ^ 2) :
    binderFromMoments a₁ b₁ < binderFromMoments a₂ b₂ := by
  have hp₁ : 0 < a₁ ^ 2 := sq_pos_of_pos ha₁
  have hp₂ : 0 < a₂ ^ 2 := sq_pos_of_pos ha₂
  have hr₁ : c < b₁ / a₁ ^ 2 :=
    (lt_div_iff₀ hp₁).mpr (by nlinarith [h₁])
  have hr₂ : b₂ / a₂ ^ 2 < c :=
    (div_lt_iff₀ hp₂).mpr (by nlinarith [h₂])
  have hs₁ : binderFromMoments a₁ b₁ = 1 - (b₁ / a₁ ^ 2) / 3 := by
    unfold binderFromMoments
    ring
  have hs₂ : binderFromMoments a₂ b₂ = 1 - (b₂ / a₂ ^ 2) / 3 := by
    unfold binderFromMoments
    ring
  rw [hs₁, hs₂]
  linarith

theorem centered_binder_interval (a b c a₀ e gLower gUpper : ℝ)
    (hc : 0 ≤ c) (he : |a - a₀| ≤ e)
    (hGlo : gLower ≤ b - 2 * c * a₀ * a + c * a₀ ^ 2)
    (hGhi : b - 2 * c * a₀ * a + c * a₀ ^ 2 ≤ gUpper) :
    gLower - c * e ^ 2 ≤ b - c * a ^ 2 ∧
      b - c * a ^ 2 ≤ gUpper := by
  have ⟨helo, hehi⟩ := abs_le.mp he
  have he' : (a - a₀) ^ 2 ≤ e ^ 2 := by nlinarith
  have hid := centered_binder_identity a b c a₀
  constructor <;> nlinarith [sq_nonneg (a - a₀)]

/-- The actual centered sign certificate is a probability statement, not a
    deterministic theorem about finite data. The two input coverage claims
    are supplied by an external bounded-iid concentration theorem. -/
theorem centered_binder_confidence_of_cover
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (a b c a₀ : ℝ) (e gLower gUpper : Ω → ℝ)
    (αa αg : ℝ) (hc : 0 ≤ c)
    (A B : Set Ω)
    (hAdef : A = {ω | |a - a₀| ≤ e ω})
    (hBdef : B = {ω | gLower ω ≤ b - 2 * c * a₀ * a + c * a₀ ^ 2 ∧
      b - 2 * c * a₀ * a + c * a₀ ^ 2 ≤ gUpper ω})
    (hBmeas : MeasurableSet B)
    (hA : 1 - αa ≤ μ.real A) (hB : 1 - αg ≤ μ.real B) :
    1 - (αa + αg) ≤ μ.real {ω |
      gLower ω - c * e ω ^ 2 ≤ b - c * a ^ 2 ∧
        b - c * a ^ 2 ≤ gUpper ω} := by
  have hsub : A ∩ B ⊆ {ω |
      gLower ω - c * e ω ^ 2 ≤ b - c * a ^ 2 ∧
        b - c * a ^ 2 ≤ gUpper ω} := by
    intro ω hω
    rcases hω with ⟨ha, hg⟩
    rw [hAdef] at ha
    rw [hBdef] at hg
    exact centered_binder_interval a b c a₀ (e ω) (gLower ω) (gUpper ω)
      hc ha hg.1 hg.2
  have hU : μ.real (A ∪ B) ≤ 1 := by
    calc
      μ.real (A ∪ B) ≤ μ.real Set.univ := MeasureTheory.measureReal_mono (Set.subset_univ _)
      _ = 1 := MeasureTheory.probReal_univ
  have hsum := MeasureTheory.measureReal_union_add_inter₀ hBmeas.nullMeasurableSet
    (s := A) (t := B) (MeasureTheory.measure_ne_top μ A)
      (MeasureTheory.measure_ne_top μ B)
  have hmono := MeasureTheory.measureReal_mono hsub (MeasureTheory.measure_ne_top μ _)
  linarith

/-- Four certified ratio signs at two parameters imply a crossing of the
    corresponding exact finite-volume Binder curves. This says nothing about
    the infinite-volume critical point or critical exponents. -/
theorem finiteBinder_crossing_of_ratio_signs {L₁ L₂ : ℕ}
    (f₂₁ f₄₁ : Spin L₁ → ℝ) (f₂₂ f₄₂ : Spin L₂ → ℝ)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (cₐ cᵦ : ℝ)
    (hM₁ : ∀ r ∈ Set.Icc a b, realMoment f₂₁ r ≠ 0)
    (hM₂ : ∀ r ∈ Set.Icc a b, realMoment f₂₂ r ≠ 0)
    (hp₁ₐ : 0 < realExpectation f₂₁ a)
    (hp₂ₐ : 0 < realExpectation f₂₂ a)
    (hp₁ᵦ : 0 < realExpectation f₂₁ b)
    (hp₂ᵦ : 0 < realExpectation f₂₂ b)
    (h₁ₐ : cₐ * realExpectation f₂₁ a ^ 2 < realExpectation f₄₁ a)
    (h₂ₐ : realExpectation f₄₂ a < cₐ * realExpectation f₂₂ a ^ 2)
    (h₁ᵦ : realExpectation f₄₁ b < cᵦ * realExpectation f₂₁ b ^ 2)
    (h₂ᵦ : cᵦ * realExpectation f₂₂ b ^ 2 < realExpectation f₄₂ b) :
    ∃ r ∈ Set.Ioo a b,
      realBinder f₂₁ f₄₁ r = realBinder f₂₂ f₄₂ r := by
  have hma : a ∈ Set.Icc a b := ⟨le_refl _, hab.le⟩
  have hmb : b ∈ Set.Icc a b := ⟨hab.le, le_refl _⟩
  have hlo := binder_order_of_ratio_separator
    (realExpectation f₂₁ a) (realExpectation f₄₁ a)
    (realExpectation f₂₂ a) (realExpectation f₄₂ a) cₐ
    hp₁ₐ hp₂ₐ h₁ₐ h₂ₐ
  have hhi := binder_order_of_ratio_separator
    (realExpectation f₂₂ b) (realExpectation f₄₂ b)
    (realExpectation f₂₁ b) (realExpectation f₄₁ b) cᵦ
    hp₂ᵦ hp₁ᵦ h₂ᵦ h₁ᵦ
  have hlo' : realBinder f₂₁ f₄₁ a - realBinder f₂₂ f₄₂ a < 0 := by
    rw [← expectedBinder_eq_realBinder f₂₁ f₄₁ a ha (hM₁ a hma),
      ← expectedBinder_eq_realBinder f₂₂ f₄₂ a ha (hM₂ a hma)]
    exact sub_neg.mpr hlo
  have hhi' : 0 < realBinder f₂₁ f₄₁ b - realBinder f₂₂ f₄₂ b := by
    rw [← expectedBinder_eq_realBinder f₂₁ f₄₁ b (lt_trans ha hab) (hM₁ b hmb),
      ← expectedBinder_eq_realBinder f₂₂ f₄₂ b (lt_trans ha hab) (hM₂ b hmb)]
    exact sub_pos.mpr hhi
  exact finiteBinder_crossing f₂₁ f₄₁ f₂₂ f₄₂ hab hM₁ hM₂ hlo' hhi'

/-- A finite Fourier amplitude with unit-bounded site contributions cannot
    exceed the number of sites. This supplies the distribution-free support
    bound for each spin structure-factor sample used by empirical Bernstein. -/
theorem finite_fourier_amplitude_bound {ι : Type*} [Fintype ι]
    (f : ι → ℂ) (hf : ∀ i, ‖f i‖ ≤ 1) :
    ‖∑ i, f i‖ ≤ (Fintype.card ι : ℝ) := by
  calc
    ‖∑ i, f i‖ ≤ ∑ i, ‖f i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, (1 : ℝ) := Finset.sum_le_sum (by
      intro i _
      exact hf i)
    _ = (Fintype.card ι : ℝ) := by simp

theorem finite_mode_power_bound {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℂ) (hf : ∀ i, ‖f i‖ ≤ 1) :
    0 ≤ ‖∑ i, f i‖ ^ 2 / (Fintype.card ι : ℝ) ∧
      ‖∑ i, f i‖ ^ 2 / (Fintype.card ι : ℝ) ≤ (Fintype.card ι : ℝ) := by
  have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hnorm := finite_fourier_amplitude_bound f hf
  have hsq : ‖∑ i, f i‖ ^ 2 ≤ (Fintype.card ι : ℝ) ^ 2 := by
    nlinarith [norm_nonneg (∑ i, f i)]
  constructor
  · positivity
  · apply (div_le_iff₀ hcard).2
    nlinarith

/-- Simultaneous positive structure-factor intervals propagate to a size
    quotient interval. Statistical coverage remains a separate premise. -/
theorem positive_ratio_interval (la ua lb ub a b : ℝ)
    (hla : 0 < la) (hal : la ≤ a) (hau : a ≤ ua)
    (hlb : 0 ≤ lb) (hbl : lb ≤ b) (hbu : b ≤ ub) :
    lb / ua ≤ b / a ∧ b / a ≤ ub / la := by
  have ha : 0 < a := lt_of_lt_of_le hla hal
  have hua : 0 < ua := lt_of_lt_of_le ha hau
  have hub : 0 ≤ ub := le_trans (le_trans hlb hbl) hbu
  constructor
  · exact (div_le_div_of_nonneg_left hlb ha hau).trans
      (div_le_div_of_nonneg_right hbl ha.le)
  · exact (div_le_div_of_nonneg_right hbu ha.le).trans
      (div_le_div_of_nonneg_left hub hla hal)

end GrandCanonical
