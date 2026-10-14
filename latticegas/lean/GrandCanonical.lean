import LatticeGas

/-!
Finite zero-field Ising model and the deterministic core of monotone CFTP.
`Bool.true` is spin +1.  The finite update-stream certificate does not, by itself,
assert that a pseudorandom stream is random or that a stopped sample is stationary.
-/
namespace GrandCanonical

open LatticeGas

abbrev Spin (L : ℕ) := Site L → Bool

theorem finite_spin_space (L : ℕ) : Finite (Spin L) := inferInstance

def disagreeCount {L : ℕ} (s : Spin L) : ℕ :=
  ∑ b : Bond L, if s b.1 != s (shift b) then 1 else 0

def weight {L : ℕ} (r : ℚ) (s : Spin L) : ℚ := r ^ disagreeCount s

theorem weight_nonneg {L : ℕ} (r : ℚ) (hr : 0 ≤ r) (s : Spin L) :
    0 ≤ weight r s := pow_nonneg hr _

def partition {L : ℕ} (r : ℚ) : ℚ := ∑ s : Spin L, weight r s

theorem partition_pos {L : ℕ} (r : ℚ) (hr : 0 < r) : 0 < partition (L := L) r := by
  classical
  unfold partition
  exact Finset.sum_pos (fun s _ => pow_pos hr _) (Finset.univ_nonempty)

def equilibrium {L : ℕ} (r : ℚ) (s : Spin L) : ℚ :=
  weight r s / partition (L := L) r

theorem equilibrium_nonneg {L : ℕ} (r : ℚ) (hr : 0 < r) (s : Spin L) :
    0 ≤ equilibrium r s :=
  div_nonneg (weight_nonneg r hr.le s) (partition_pos r hr).le

theorem equilibrium_sum {L : ℕ} (r : ℚ) (hr : 0 < r) :
    ∑ s : Spin L, equilibrium r s = 1 := by
  classical
  simp only [equilibrium, ← Finset.sum_div]
  exact div_self (ne_of_gt (partition_pos (L := L) r hr))

/-! The Edwards--Sokal edge factor. Its bond marginal is exactly rational. -/
def edgeJoint (r : ℚ) (agree active : Bool) : ℚ :=
  if active then (if agree then 1-r else 0) else r

theorem edgeJoint_sum (r : ℚ) (agree : Bool) :
    (∑ active : Bool, edgeJoint r agree active) =
      if agree then 1 else r := by
  cases agree <;> simp [edgeJoint, add_comm]

def jointWeight {L : ℕ} (r : ℚ) (s : Spin L) (active : Bond L → Bool) : ℚ :=
  ∏ b : Bond L, edgeJoint r (s b.1 == s (shift b)) (active b)

theorem joint_spin_marginal {L : ℕ} (r : ℚ) (s : Spin L) :
    (∑ active : Bond L → Bool, jointWeight r s active) = weight r s := by
  classical
  unfold jointWeight
  rw [← Fintype.piFinset_univ, Finset.sum_prod_piFinset]
  simp_rw [edgeJoint_sum]
  unfold weight disagreeCount
  simp only [beq_iff_eq]
  have hsum : (∑ b : Bond L, if (s b.1 != s (shift b)) = true then 1 else 0) =
      (Finset.univ.filter fun b : Bond L => s b.1 ≠ s (shift b)).card := by
    have aux (t : Finset (Bond L)) :
        t.sum (fun b => if s b.1 = s (shift b) then 0 else 1) =
          (t.filter fun b => s b.1 ≠ s (shift b)).card := by
      induction t using Finset.induction_on with
      | empty => simp
      | @insert b t hb ih =>
          by_cases he : s b.1 = s (shift b) <;>
            simp [Finset.filter_insert, he, hb, ih, add_comm]
    simpa using aux Finset.univ
  rw [hsum]
  have hprod : (∏ b : Bond L, if s b.1 = s (shift b) then (1 : ℚ) else r) =
      ∏ b : Bond L, if s b.1 ≠ s (shift b) then r else 1 := by
    apply Finset.prod_congr rfl
    intro b _
    by_cases he : s b.1 = s (shift b) <;> simp [he]
  rw [hprod, Finset.prod_ite]
  simp

/-! Six directed neighbours, counted with multiplicity (important at small L). -/
def prevIndex {L : ℕ} (hL : 0 < L) (x : Fin L) : Fin L :=
  ⟨(x.val + L - 1) % L, Nat.mod_lt _ hL⟩

def neighbour {L : ℕ} (hL : 0 < L) (x : Site L) : Fin 6 → Site L
  | ⟨0, _⟩ => (nextIndex x.1, x.2.1, x.2.2)
  | ⟨1, _⟩ => (prevIndex hL x.1, x.2.1, x.2.2)
  | ⟨2, _⟩ => (x.1, nextIndex x.2.1, x.2.2)
  | ⟨3, _⟩ => (x.1, prevIndex hL x.2.1, x.2.2)
  | ⟨4, _⟩ => (x.1, x.2.1, nextIndex x.2.2)
  | _ => (x.1, x.2.1, prevIndex hL x.2.2)

def plusCount {L : ℕ} (hL : 0 < L) (s : Spin L) (x : Site L) : ℕ :=
  ∑ i : Fin 6, (s (neighbour hL x i)).toNat

def spinLE {L : ℕ} (s t : Spin L) : Prop :=
  ∀ x, s x = true → t x = true

theorem bottom_le {L : ℕ} (s : Spin L) : spinLE (fun _ => false) s := by
  intro x h
  cases h

theorem le_top {L : ℕ} (s : Spin L) : spinLE s (fun _ => true) := by
  intro x h
  rfl

theorem plusCount_mono {L : ℕ} (hL : 0 < L) {s t : Spin L}
    (hst : spinLE s t) (x : Site L) : plusCount hL s x ≤ plusCount hL t x := by
  unfold plusCount
  apply Finset.sum_le_sum
  intro i _
  cases hs : s (neighbour hL x i) with
  | false => simp
  | true => simp [hst _ hs]

def heatProb (r : ℚ) (a : ℕ) : ℚ :=
  r ^ (6 - a) / (r ^ (6 - a) + r ^ a)

theorem heatProb_mono (r : ℚ) (hr : 0 < r) (hr1 : r ≤ 1)
    {a b : ℕ} (hab : a ≤ b) : heatProb r a ≤ heatProb r b := by
  have hA : r ^ (6 - a) ≤ r ^ (6 - b) :=
    pow_le_pow_of_le_one hr.le hr1 (by omega)
  have hB : r ^ b ≤ r ^ a :=
    pow_le_pow_of_le_one hr.le hr1 hab
  have hAa : 0 ≤ r ^ (6-a) := pow_nonneg hr.le _
  have hAb : 0 ≤ r ^ (6-b) := pow_nonneg hr.le _
  have hBa : 0 ≤ r ^ a := pow_nonneg hr.le _
  have hBb : 0 ≤ r ^ b := pow_nonneg hr.le _
  have hdena : 0 < r ^ (6-a) + r ^ a := add_pos (pow_pos hr _) (pow_pos hr _)
  have hdenb : 0 < r ^ (6-b) + r ^ b := add_pos (pow_pos hr _) (pow_pos hr _)
  unfold heatProb
  apply (div_le_div_iff₀ hdena hdenb).2
  nlinarith [mul_nonneg (sub_nonneg.mpr hA) hBb,
    mul_nonneg hAb (sub_nonneg.mpr hB)]

theorem heatProb_nonneg (r : ℚ) (hr : 0 < r) (a : ℕ) :
    0 ≤ heatProb r a := by
  unfold heatProb
  positivity

theorem heatProb_le_one (r : ℚ) (hr : 0 < r) (a : ℕ) :
    heatProb r a ≤ 1 := by
  unfold heatProb
  have h1 : 0 ≤ r ^ a := pow_nonneg hr.le _
  have h2 : 0 < r ^ (6-a) + r ^ a := add_pos (pow_pos hr _) (pow_pos hr _)
  exact (div_le_one h2).2 (by linarith)

/-! This is the exact integer comparison used by the C++ implementation. -/
theorem rational_threshold (u M n d : ℕ) (hM : 0 < M) (hd : 0 < d) :
    ((u : ℚ) / M < (n : ℚ) / d) ↔ u * d < M * n := by
  have hM' : (0 : ℚ) < M := by exact_mod_cast hM
  have hd' : (0 : ℚ) < d := by exact_mod_cast hd
  rw [div_lt_div_iff₀ hM' hd']
  exact_mod_cast (show u * d < n * M ↔ u * d < M * n by simp [mul_comm])

def update {L : ℕ} (hL : 0 < L) (p : ℕ → ℚ)
    (x : Site L) (u : ℚ) (s : Spin L) : Spin L :=
  fun y => if y = x then decide (u < p (plusCount hL s x)) else s y

theorem update_mono {L : ℕ} (hL : 0 < L) (p : ℕ → ℚ)
    (hp : Monotone p) (x : Site L) (u : ℚ) {s t : Spin L}
    (hst : spinLE s t) : spinLE (update hL p x u s) (update hL p x u t) := by
  intro y hy
  by_cases h : y = x
  · subst y
    simp only [update, ↓reduceIte] at hy ⊢
    have hlt : u < p (plusCount hL s x) := of_decide_eq_true hy
    exact decide_eq_true (lt_of_lt_of_le hlt (hp (plusCount_mono hL hst x)))
  · simpa [update, h] using hst y (by simpa [update, h] using hy)

abbrev Instruction (L : ℕ) := Site L × ℚ

def replay {L : ℕ} (hL : 0 < L) (p : ℕ → ℚ)
    (stream : List (Instruction L)) (s : Spin L) : Spin L :=
  stream.foldl (fun z i => update hL p i.1 i.2 z) s

theorem replay_mono {L : ℕ} (hL : 0 < L) (p : ℕ → ℚ)
    (hp : Monotone p) (stream : List (Instruction L)) {s t : Spin L}
    (hst : spinLE s t) : spinLE (replay hL p stream s) (replay hL p stream t) := by
  induction stream generalizing s t with
  | nil => exact hst
  | cons i rest ih =>
      exact ih (update_mono hL p hp i.1 i.2 hst)

theorem spinLE_antisymm {L : ℕ} {s t : Spin L}
    (hst : spinLE s t) (hts : spinLE t s) : s = t := by
  funext x
  cases hs : s x <;> cases ht : t x <;> simp_all [spinLE]

/-! The replayed finite stream is a proof certificate for *all-start* coalescence. -/
theorem coalescence_certificate {L : ℕ} (hL : 0 < L)
    (p : ℕ → ℚ) (hp : Monotone p) (stream : List (Instruction L))
    (hcoal : replay hL p stream (fun _ => false) =
      replay hL p stream (fun _ => true)) (s : Spin L) :
    replay hL p stream s = replay hL p stream (fun _ => false) := by
  apply spinLE_antisymm
  · rw [hcoal]
    exact replay_mono hL p hp stream (le_top s)
  · exact replay_mono hL p hp stream (bottom_le s)

/-!
The probabilistic CFTP conclusion is deliberately conditional on a stationary
reference trajectory driven by the same *ideal* past update stream. The finite
replay certificate proves the coupling step; it does not prove that a seeded
PRNG supplies the ideal law or construct the two-sided stationary process.
-/
theorem cftp_stationary_of_stationary_coupling {L : ℕ} (hL : 0 < L)
    (p : ℕ → ℚ) (hp : Monotone p)
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (stream : Ω → List (Instruction L))
    (past final : Ω → Spin L)
    (hcoal : ∀ ω, replay hL p (stream ω) (fun _ => false) =
      replay hL p (stream ω) (fun _ => true))
    (htrajectory : ∀ ω, replay hL p (stream ω) (past ω) = final ω)
    (hstationary : MeasureTheory.Measure.map final μ =
      MeasureTheory.Measure.map past μ) :
    MeasureTheory.Measure.map
        (fun ω => replay hL p (stream ω) (fun _ => false)) μ =
      MeasureTheory.Measure.map past μ := by
  have heq : (fun ω => replay hL p (stream ω) (fun _ => false)) = final := by
    funext ω
    exact (coalescence_certificate hL p hp (stream ω) (hcoal ω) (past ω)).symm.trans
      (htrajectory ω)
  rw [heq]
  exact hstationary

/-! Deterministic interval propagation; confidence coverage is a separate premise. -/
def binder (m₂ m₄ : ℚ) : ℚ := 1 - m₄ / (3 * m₂ ^ 2)

theorem binder_interval (l₂ u₂ l₄ u₄ m₂ m₄ : ℚ)
    (hl₂ : 0 < l₂) (hm₂l : l₂ ≤ m₂) (hm₂u : m₂ ≤ u₂)
    (hl₄ : 0 ≤ l₄) (hm₄l : l₄ ≤ m₄) (hm₄u : m₄ ≤ u₄) :
    1 - u₄ / (3 * l₂ ^ 2) ≤ binder m₂ m₄ ∧
      binder m₂ m₄ ≤ 1 - l₄ / (3 * u₂ ^ 2) := by
  have hm₂ : 0 < m₂ := lt_of_lt_of_le hl₂ hm₂l
  have hu₂ : 0 < u₂ := lt_of_lt_of_le hm₂ hm₂u
  have hm₄ : 0 ≤ m₄ := le_trans hl₄ hm₄l
  have hu₄ : 0 ≤ u₄ := le_trans hm₄ hm₄u
  have hdenl : 0 < 3 * l₂ ^ 2 := by positivity
  have hdenm : 0 < 3 * m₂ ^ 2 := by positivity
  have hdenu : 0 < 3 * u₂ ^ 2 := by positivity
  have hml : 3 * l₂ ^ 2 ≤ 3 * m₂ ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hm₂l) (add_nonneg hm₂.le hl₂.le)]
  have hum : 3 * m₂ ^ 2 ≤ 3 * u₂ ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hm₂u) (add_nonneg hu₂.le hm₂.le)]
  have hr1 : m₄ / (3 * m₂ ^ 2) ≤ u₄ / (3 * l₂ ^ 2) := by
    exact (div_le_div_of_nonneg_right hm₄u hdenm.le).trans
      (div_le_div_of_nonneg_left hu₄ hdenl hml)
  have hr2 : l₄ / (3 * u₂ ^ 2) ≤ m₄ / (3 * m₂ ^ 2) := by
    exact (div_le_div_of_nonneg_left hl₄ hdenm hum).trans
      (div_le_div_of_nonneg_right hm₄l hdenm.le)
  constructor <;> unfold binder <;> linarith

theorem binder_confidence_of_moment_cover
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (l₂ u₂ l₄ u₄ : Ω → ℚ) (m₂ m₄ : ℚ) (α₂ α₄ : ℝ)
    (A : Set Ω) (B : Set Ω)
    (hAdef : A = {ω | 0 < l₂ ω ∧ l₂ ω ≤ m₂ ∧ m₂ ≤ u₂ ω})
    (hBdef : B = {ω | 0 ≤ l₄ ω ∧ l₄ ω ≤ m₄ ∧ m₄ ≤ u₄ ω})
    (hBmeas : MeasurableSet B)
    (hA : 1 - α₂ ≤ μ.real A) (hB : 1 - α₄ ≤ μ.real B) :
    1 - (α₂ + α₄) ≤ μ.real {ω |
      1 - u₄ ω / (3 * l₂ ω ^ 2) ≤ binder m₂ m₄ ∧
        binder m₂ m₄ ≤ 1 - l₄ ω / (3 * u₂ ω ^ 2)} := by
  have hsub : A ∩ B ⊆ {ω |
      1 - u₄ ω / (3 * l₂ ω ^ 2) ≤ binder m₂ m₄ ∧
        binder m₂ m₄ ≤ 1 - l₄ ω / (3 * u₂ ω ^ 2)} := by
    intro ω hω
    rcases hω with ⟨ha, hb⟩
    rw [hAdef] at ha
    rw [hBdef] at hb
    exact binder_interval (l₂ ω) (u₂ ω) (l₄ ω) (u₄ ω) m₂ m₄
      ha.1 ha.2.1 ha.2.2 hb.1 hb.2.1 hb.2.2
  have hU : μ.real (A ∪ B) ≤ 1 := by
    calc
      μ.real (A ∪ B) ≤ μ.real Set.univ := MeasureTheory.measureReal_mono (Set.subset_univ _)
      _ = 1 := MeasureTheory.probReal_univ
  have hsum := MeasureTheory.measureReal_union_add_inter₀ hBmeas.nullMeasurableSet
    (s := A) (t := B) (MeasureTheory.measure_ne_top μ A)
      (MeasureTheory.measure_ne_top μ B)
  have hmono := MeasureTheory.measureReal_mono hsub (MeasureTheory.measure_ne_top μ _)
  linarith

/-! Crossing logic; establishing continuity of a concrete curve is separate. -/
theorem crossing_of_endpoint_signs {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hf : ContinuousOn f (Set.Icc a b))
    (ha : f a < 0) (hb : 0 < f b) :
    ∃ r ∈ Set.Ioo a b, f r = 0 := by
  obtain ⟨r, hr, hfr⟩ := (intermediate_value_Icc hab.le hf)
    (show (0 : ℝ) ∈ Set.Icc (f a) (f b) from ⟨ha.le, hb.le⟩)
  refine ⟨r, ⟨?_, ?_⟩, hfr⟩
  · rcases hr with ⟨hlo, hhi⟩
    exact lt_of_le_of_ne hlo (by
      intro he
      have : f a = 0 := by simpa [he] using hfr
      exact (ne_of_lt ha) this)
  · rcases hr with ⟨hlo, hhi⟩
    exact lt_of_le_of_ne hhi (by
      intro he
      have : f b = 0 := by simpa [he] using hfr
      exact (ne_of_gt hb) this)

/-! Every finite-volume moment is a polynomial in r; its Binder ratio is
continuous wherever the second moment is nonzero. -/
def realMoment {L : ℕ} (c : Spin L → ℝ) (r : ℝ) : ℝ :=
  ∑ s : Spin L, c s * r ^ disagreeCount s

theorem realMoment_continuous {L : ℕ} (c : Spin L → ℝ) :
    Continuous (realMoment c) := by
  unfold realMoment
  fun_prop

theorem realMoment_pos {L : ℕ} (c : Spin L → ℝ) (r : ℝ)
    (hr : 0 < r) (hc : ∀ s, 0 ≤ c s) (hex : ∃ s, 0 < c s) :
    0 < realMoment c r := by
  classical
  unfold realMoment
  apply Finset.sum_pos'
  · intro s _
    exact mul_nonneg (hc s) (pow_nonneg hr.le _)
  · rcases hex with ⟨s, hs⟩
    exact ⟨s, Finset.mem_univ _, mul_pos hs (pow_pos hr _)⟩

noncomputable def realBinder {L : ℕ} (c₂ c₄ : Spin L → ℝ) (r : ℝ) : ℝ :=
  1 - realMoment c₄ r * realMoment (L := L) (fun _ => 1) r /
    (3 * (realMoment c₂ r) ^ 2)

theorem realBinder_continuousOn {L : ℕ} (c₂ c₄ : Spin L → ℝ)
    {a b : ℝ} (h₂ : ∀ r ∈ Set.Icc a b, realMoment c₂ r ≠ 0) :
    ContinuousOn (realBinder c₂ c₄) (Set.Icc a b) := by
  unfold realBinder
  apply ContinuousOn.sub continuousOn_const
  apply ContinuousOn.div
  · exact ((realMoment_continuous c₄).mul
      (realMoment_continuous (fun _ => 1))).continuousOn
  · exact (continuous_const.mul ((realMoment_continuous c₂).pow 2)).continuousOn
  · intro r hr
    have hn := h₂ r hr
    positivity

theorem finiteBinder_crossing {L₁ L₂ : ℕ}
    (c₂₁ c₄₁ : Spin L₁ → ℝ) (c₂₂ c₄₂ : Spin L₂ → ℝ)
    {a b : ℝ} (hab : a < b)
    (h₂₁ : ∀ r ∈ Set.Icc a b, realMoment c₂₁ r ≠ 0)
    (h₂₂ : ∀ r ∈ Set.Icc a b, realMoment c₂₂ r ≠ 0)
    (hlo : realBinder c₂₁ c₄₁ a - realBinder c₂₂ c₄₂ a < 0)
    (hhi : 0 < realBinder c₂₁ c₄₁ b - realBinder c₂₂ c₄₂ b) :
    ∃ r ∈ Set.Ioo a b, realBinder c₂₁ c₄₁ r = realBinder c₂₂ c₄₂ r := by
  have hc : ContinuousOn
      (fun r => realBinder c₂₁ c₄₁ r - realBinder c₂₂ c₄₂ r) (Set.Icc a b) :=
    (realBinder_continuousOn c₂₁ c₄₁ h₂₁).sub
      (realBinder_continuousOn c₂₂ c₄₂ h₂₂)
  obtain ⟨r, hr, hzero⟩ := crossing_of_endpoint_signs hab hc hlo hhi
  exact ⟨r, hr, sub_eq_zero.mp hzero⟩

theorem finiteBinder_crossing_positive {L₁ L₂ : ℕ}
    (c₂₁ c₄₁ : Spin L₁ → ℝ) (c₂₂ c₄₂ : Spin L₂ → ℝ)
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hn₁ : ∀ s, 0 ≤ c₂₁ s) (hp₁ : ∃ s, 0 < c₂₁ s)
    (hn₂ : ∀ s, 0 ≤ c₂₂ s) (hp₂ : ∃ s, 0 < c₂₂ s)
    (hlo : realBinder c₂₁ c₄₁ a - realBinder c₂₂ c₄₂ a < 0)
    (hhi : 0 < realBinder c₂₁ c₄₁ b - realBinder c₂₂ c₄₂ b) :
    ∃ r ∈ Set.Ioo a b, realBinder c₂₁ c₄₁ r = realBinder c₂₂ c₄₂ r := by
  apply finiteBinder_crossing c₂₁ c₄₁ c₂₂ c₄₂ hab
  · intro r hr
    exact ne_of_gt (realMoment_pos c₂₁ r (lt_of_lt_of_le ha hr.1) hn₁ hp₁)
  · intro r hr
    exact ne_of_gt (realMoment_pos c₂₂ r (lt_of_lt_of_le ha hr.1) hn₂ hp₂)
  · exact hlo
  · exact hhi

def magnetizationSum {L : ℕ} (s : Spin L) : ℤ :=
  ∑ x : Site L, if s x then 1 else -1

def magnetizationSq {L : ℕ} (s : Spin L) : ℝ :=
  (magnetizationSum s : ℝ) ^ 2

def magnetizationFourth {L : ℕ} (s : Spin L) : ℝ :=
  (magnetizationSum s : ℝ) ^ 4

theorem magnetizationSq_nonneg {L : ℕ} (s : Spin L) :
    0 ≤ magnetizationSq s := by
  unfold magnetizationSq
  positivity

theorem magnetizationSq_exists_pos (L : ℕ) (hL : 0 < L) :
    ∃ s : Spin L, 0 < magnetizationSq s := by
  let x : Fin L := ⟨0, hL⟩
  let site : Site L := (x,x,x)
  have hcard : 0 < Fintype.card (Site L) := Fintype.card_pos_iff.mpr ⟨site⟩
  refine ⟨fun _ => true, ?_⟩
  have hmag : magnetizationSum (fun _ : Site L => true) =
      (Fintype.card (Site L) : ℤ) := by
    simp [magnetizationSum]
  unfold magnetizationSq
  rw [hmag]
  have hreal : (0 : ℝ) < Fintype.card (Site L) := by exact_mod_cast hcard
  positivity

theorem isingBinder_crossing {L₁ L₂ : ℕ}
    (hL₁ : 0 < L₁) (hL₂ : 0 < L₂)
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hlo : realBinder (L := L₁) magnetizationSq magnetizationFourth a -
      realBinder (L := L₂) magnetizationSq magnetizationFourth a < 0)
    (hhi : 0 < realBinder (L := L₁) magnetizationSq magnetizationFourth b -
      realBinder (L := L₂) magnetizationSq magnetizationFourth b) :
    ∃ r ∈ Set.Ioo a b,
      realBinder (L := L₁) magnetizationSq magnetizationFourth r =
        realBinder (L := L₂) magnetizationSq magnetizationFourth r := by
  exact finiteBinder_crossing_positive
    magnetizationSq magnetizationFourth magnetizationSq magnetizationFourth
    ha hab (fun s => magnetizationSq_nonneg s) (magnetizationSq_exists_pos L₁ hL₁)
    (fun s => magnetizationSq_nonneg s) (magnetizationSq_exists_pos L₂ hL₂) hlo hhi

end GrandCanonical
