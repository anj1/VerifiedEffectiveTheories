import Grain.Pairing

/-! Enclosures for material inputs on a finite mesh. Energies and the
Fermi window half width are in meV. The unknown values in the boxes can
be real, even though the certificate arithmetic is rational. -/

namespace Grain.Pairing.Material

structure Interval where
  lo : ℚ
  hi : ℚ
  deriving DecidableEq

namespace Interval

def contains (b : Interval) (x : ℝ) : Prop := (b.lo : ℝ) ≤ x ∧ x ≤ (b.hi : ℝ)

def point (x : ℚ) : Interval := ⟨x, x⟩
def add (a b : Interval) : Interval := ⟨a.lo + b.lo, a.hi + b.hi⟩
def sub (a b : Interval) : Interval := ⟨a.lo - b.hi, a.hi - b.lo⟩
def nonneg (a : Interval) : Interval := ⟨max 0 a.lo, a.hi⟩
def mulPos (a b : Interval) : Interval := ⟨a.lo * b.lo, a.hi * b.hi⟩
def divPos (a b : Interval) : Interval := ⟨a.lo / b.hi, a.hi / b.lo⟩
def mid (a : Interval) : ℚ := (a.lo + a.hi) / 2
def radius (a : Interval) (c : ℚ) : ℚ := max |a.lo - c| |a.hi - c|
def sum [Fintype ι] (b : ι → Interval) : Interval := ⟨∑ i, (b i).lo, ∑ i, (b i).hi⟩
def sumList (bs : List Interval) : Interval :=
  ⟨(bs.map (·.lo)).sum, (bs.map (·.hi)).sum⟩

theorem point_contains (x : ℚ) : (point x).contains (x : ℝ) := ⟨le_rfl, le_rfl⟩

theorem add_contains {a b : Interval} {x y : ℝ}
    (hx : a.contains x) (hy : b.contains y) : (a.add b).contains (x + y) := by
  exact ⟨by simpa [add] using add_le_add hx.1 hy.1, by simpa [add] using add_le_add hx.2 hy.2⟩

theorem sub_contains {a b : Interval} {x y : ℝ}
    (hx : a.contains x) (hy : b.contains y) : (a.sub b).contains (x - y) := by
  exact ⟨by simpa [sub] using sub_le_sub hx.1 hy.2, by simpa [sub] using sub_le_sub hx.2 hy.1⟩

theorem nonneg_contains {a : Interval} {x : ℝ} (h : a.contains x) (hx : 0 ≤ x) :
    a.nonneg.contains x := ⟨by simpa [nonneg] using max_le hx h.1, h.2⟩

theorem mul_contains {a b : Interval} {x y : ℝ}
    (ha : 0 ≤ a.lo) (hb : 0 ≤ b.lo) (hx : a.contains x) (hy : b.contains y) :
    (a.mulPos b).contains (x * y) := by
  have ha' : (0 : ℝ) ≤ a.lo := by exact_mod_cast ha
  have hb' : (0 : ℝ) ≤ b.lo := by exact_mod_cast hb
  exact ⟨by simpa [mulPos] using mul_le_mul hx.1 hy.1 hb' (ha'.trans hx.1),
    by simpa [mulPos] using mul_le_mul hx.2 hy.2 (hb'.trans hy.1) (ha'.trans (hx.1.trans hx.2))⟩

theorem div_contains {a b : Interval} {x y : ℝ}
    (ha : 0 ≤ a.lo) (hb : 0 < b.lo) (hx : a.contains x) (hy : b.contains y) :
    (a.divPos b).contains (x / y) := by
  have ha' : (0 : ℝ) ≤ a.lo := by exact_mod_cast ha
  have hb' : (0 : ℝ) < b.lo := by exact_mod_cast hb
  have hy' := hb'.trans_le hy.1
  constructor
  · simpa [divPos] using (div_le_div_of_nonneg_left ha' hy' hy.2).trans
      (div_le_div_of_nonneg_right hx.1 hy'.le)
  · simpa [divPos] using (div_le_div_of_nonneg_right hx.2 hy'.le).trans
      (div_le_div_of_nonneg_left (ha'.trans (hx.1.trans hx.2)) hb' hy.1)

theorem sum_contains [Fintype ι] (b : ι → Interval) (v : ι → ℝ)
    (h : ∀ i, (b i).contains (v i)) : (sum b).contains (∑ i, v i) := by
  exact ⟨by simpa [sum] using Finset.sum_le_sum (fun i _ => (h i).1),
    by simpa [sum] using Finset.sum_le_sum (fun i _ => (h i).2)⟩

theorem sumList_contains {bs : List Interval} {vs : List ℝ}
    (h : List.Forall₂ contains bs vs) : (sumList bs).contains vs.sum := by
  induction h with
  | nil => simp [sumList, contains]
  | @cons b v bs vs hv hbs ih =>
    exact add_contains hv ih

theorem abs_sub_le_radius {a : Interval} {x : ℝ} (h : a.contains x) (c : ℚ) :
    |x - (c : ℝ)| ≤ (a.radius c : ℝ) := by
  rw [radius, Rat.cast_max, Rat.cast_abs, Rat.cast_abs, Rat.cast_sub, Rat.cast_sub]
  have hl := le_max_left (abs ((a.lo : ℝ) - c)) (abs ((a.hi : ℝ) - c))
  have hh := le_max_right (abs ((a.lo : ℝ) - c)) (abs ((a.hi : ℝ) - c))
  exact abs_le.2 ⟨by linarith only [h.1, neg_abs_le ((a.lo : ℝ) - c), hl],
    by linarith only [h.2, le_abs_self ((a.hi : ℝ) - c), hh]⟩

end Interval

structure Sample where
  energy : Interval
  weight : ℚ

def windowSample (h : ℚ) (s : Sample) : Interval :=
  if -h ≤ s.energy.lo ∧ s.energy.hi ≤ h then Interval.point s.weight
  else if s.energy.hi < -h ∨ h < s.energy.lo then Interval.point 0
  else ⟨0, s.weight⟩

noncomputable def sampledWeight (h : ℚ) (s : Sample) (energy : ℝ) : ℝ :=
  if -(h : ℝ) ≤ energy ∧ energy ≤ h then s.weight else 0

theorem window_contains (h : ℚ) (s : Sample) (energy : ℝ) (hw : 0 ≤ s.weight)
    (he : s.energy.contains energy) : (windowSample h s).contains (sampledWeight h s energy) := by
  unfold windowSample sampledWeight
  split
  · rename_i hinside
    have h1 : -(h : ℝ) ≤ (s.energy.lo : ℝ) := by exact_mod_cast hinside.1
    have h2 : (s.energy.hi : ℝ) ≤ h := by exact_mod_cast hinside.2
    rw [ite_eq_left ⟨h1.trans he.1, he.2.trans h2⟩]
    exact Interval.point_contains _
  · split
    · rename_i hout
      have hout' : ¬ (-(h : ℝ) ≤ energy ∧ energy ≤ h) := by
        intro h'
        rcases hout with hlt | hlt
        · have hlt' : (s.energy.hi : ℝ) < -(h : ℝ) := by exact_mod_cast hlt
          linarith only [he.2, h'.1, hlt']
        · have hlt' : (h : ℝ) < s.energy.lo := by exact_mod_cast hlt
          linarith only [he.1, h'.2, hlt']
      rw [ite_eq_right hout']
      simpa using Interval.point_contains 0
    · have hw' : (0 : ℝ) ≤ s.weight := by exact_mod_cast hw
      split
      · exact ⟨by simpa using hw', le_rfl⟩
      · exact ⟨by simp, hw'⟩

def weightBox (h : ℚ) (samples : List Sample) : Interval :=
  (Interval.sumList (samples.map (windowSample h))).divPos (Interval.point (2 * h))

noncomputable def meshWeight (h : ℚ) (samples : List Sample) (energies : List ℝ) : ℝ :=
  ((samples.zipWith (sampledWeight h) energies).sum) / (2 * (h : ℝ))

def sampled (samples : List Sample) (energies : List ℝ) : Prop :=
  List.Forall₂ (fun s e => 0 ≤ s.weight ∧ s.energy.contains e) samples energies

theorem weight_enclosure (h : ℚ) (hh : 0 < h) (samples : List Sample) (energies : List ℝ)
    (hs : sampled samples energies) : (weightBox h samples).contains (meshWeight h samples energies) := by
  have hrows : List.Forall₂ Interval.contains (samples.map (windowSample h))
      (samples.zipWith (sampledWeight h) energies) := by
    induction hs with
    | nil => exact .nil
    | cons hb _ ih => exact .cons (window_contains h _ _ hb.1 hb.2) ih
  have hn : 0 ≤ (Interval.sumList (samples.map (windowSample h))).lo := by
    clear hrows
    induction hs with
    | nil => norm_num [Interval.sumList]
    | @cons s e ss es hs _ ih =>
      change 0 ≤ (windowSample h s).lo + (Interval.sumList (ss.map (windowSample h))).lo
      apply add_nonneg _ ih
      unfold windowSample
      split
      · exact hs.1
      · split <;> exact le_rfl
  have hd : 0 < (Interval.point (2 * h)).lo := by change 0 < 2 * h; positivity
  simpa [weightBox, meshWeight] using Interval.div_contains hn hd
    (Interval.sumList_contains hrows) (Interval.point_contains (2 * h))

structure ModeBox where
  energy : Interval
  vertexSq : Interval
  deriving DecidableEq

structure RealMode where
  energy : ℝ
  vertexSq : ℝ

def ModeBox.matches (b : ModeBox) (m : RealMode) : Prop :=
  0 < b.energy.lo ∧ 0 ≤ b.vertexSq.lo ∧ b.energy.contains m.energy ∧
    b.vertexSq.contains m.vertexSq

def modeEnvelope (b : ModeBox) (transferSq : ℚ) : Interval :=
  (((Interval.point 2).mulPos b.energy).mulPos b.vertexSq).divPos
    ((b.energy.mulPos b.energy).add (Interval.point transferSq))

noncomputable def modeResponse (m : RealMode) (transferSq : ℝ) : ℝ :=
  2 * m.energy * m.vertexSq / (m.energy * m.energy + transferSq)

theorem mode_enclosure (b : ModeBox) (m : RealMode) (q : ℚ) (hq : 0 ≤ q)
    (h : b.matches m) : (modeEnvelope b q).contains (modeResponse m q) := by
  obtain ⟨he, hv, hm, hg⟩ := h
  have hN : 0 ≤ (((Interval.point 2).mulPos b.energy).mulPos b.vertexSq).lo := by
    change 0 ≤ 2 * b.energy.lo * b.vertexSq.lo
    positivity
  have hD : 0 < ((b.energy.mulPos b.energy).add (Interval.point q)).lo := by
    change 0 < b.energy.lo * b.energy.lo + q
    positivity
  have hn := Interval.mul_contains (a := Interval.point 2) (by decide) he.le
    (Interval.point_contains 2) hm
  simpa [modeResponse, modeEnvelope] using Interval.div_contains hN hD
    (Interval.mul_contains (by change 0 ≤ 2 * b.energy.lo; positivity) hv hn hg)
    (Interval.add_contains (Interval.mul_contains he.le he.le hm hm) (Interval.point_contains q))

def phononEnvelope (b : List ModeBox) (q : ℚ) : Interval :=
  Interval.sumList (b.map fun m => modeEnvelope m q)

noncomputable def phononResponse (m : List RealMode) (q : ℝ) : ℝ :=
  (m.map fun m => modeResponse m q).sum

theorem phonon_enclosure (b : List ModeBox) (m : List RealMode) (q : ℚ) (hq : 0 ≤ q)
    (h : List.Forall₂ ModeBox.matches b m) :
    (phononEnvelope b q).contains (phononResponse m q) := by
  apply Interval.sumList_contains
  induction h with
  | nil => exact .nil
  | cons hm _ ih => exact .cons (mode_enclosure _ _ q hq hm) ih

theorem phonon_decreases (b : List ModeBox) (m : List RealMode) {q r : ℝ}
    (hq : 0 ≤ q) (hqr : q ≤ r) (h : List.Forall₂ ModeBox.matches b m) :
    phononResponse m r ≤ phononResponse m q := by
  induction h with
  | nil => rfl
  | @cons bi mi _ _ hmi _ ih =>
    apply add_le_add _ ih
    unfold modeResponse
    have hE : 0 < mi.energy := (by exact_mod_cast hmi.1 : (0 : ℝ) < bi.energy.lo).trans_le hmi.2.2.1.1
    have hG : 0 ≤ mi.vertexSq := (by exact_mod_cast hmi.2.1 : (0 : ℝ) ≤ bi.vertexSq.lo).trans
      hmi.2.2.2.1
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)

structure Mesh (p : Type) where
  halfWidth : ℚ
  bands : p → List Sample
  modes : p → p → List ModeBox
  coulomb : p → p → Interval

structure Realization (p : Type) where
  bands : p → List ℝ
  modes : p → p → List RealMode
  coulomb : p → p → ℝ
  integratedDOS : Option (p → ℝ) := none

def Mesh.matches (b : Mesh p) (r : Realization p) : Prop :=
  (match r.integratedDOS with
    | none => ∀ i, sampled (b.bands i) (r.bands i)
    | some w => ∀ i, (weightBox b.halfWidth (b.bands i)).contains (w i)) ∧
  (∀ i j, List.Forall₂ ModeBox.matches (b.modes i j) (r.modes i j)) ∧
  (∀ i j, 0 ≤ (b.coulomb i j).lo ∧ (b.coulomb i j).contains (r.coulomb i j))

def Mesh.valid (b : Mesh p) : Prop :=
  (∀ i, (b.bands i).Forall fun s => 0 ≤ s.weight ∧ s.energy.lo ≤ s.energy.hi) ∧
  (∀ i j, (b.modes i j).Forall fun m => 0 < m.energy.lo ∧ 0 ≤ m.vertexSq.lo ∧
    m.energy.lo ≤ m.energy.hi ∧ m.vertexSq.lo ≤ m.vertexSq.hi) ∧
  (∀ i j, 0 ≤ (b.coulomb i j).lo ∧ (b.coulomb i j).lo ≤ (b.coulomb i j).hi)

instance [Fintype p] (b : Mesh p) : Decidable (Mesh.valid b) := by
  unfold Mesh.valid
  infer_instance

def Mesh.symmetric (b : Mesh p) : Prop :=
  (∀ i j, b.modes i j = b.modes j i) ∧ (∀ i j, b.coulomb i j = b.coulomb j i)

instance [Fintype p] (b : Mesh p) : Decidable b.symmetric := by
  unfold Mesh.symmetric
  infer_instance

noncomputable def midpointRealization (b : Mesh p) : Realization p where
  bands i := (b.bands i).map fun s => (s.energy.mid : ℝ)
  modes i j := (b.modes i j).map fun m => ⟨m.energy.mid, m.vertexSq.mid⟩
  coulomb i j := (b.coulomb i j).mid

theorem midpoint_symmetric (b : Mesh p) (h : b.symmetric) :
    (∀ i j, (midpointRealization b).modes i j = (midpointRealization b).modes j i) ∧
    (∀ i j, (midpointRealization b).coulomb i j = (midpointRealization b).coulomb j i) :=
  ⟨fun i j => congrArg _ (h.1 i j), fun i j => congrArg (fun a : Interval => (a.mid : ℝ)) (h.2 i j)⟩

theorem midpoint_realizes (b : Mesh p) (h : b.valid) : b.matches (midpointRealization b) := by
  have mid (a : Interval) (ha : a.lo ≤ a.hi) : a.contains (a.mid : ℝ) := by
    have h : (a.lo : ℝ) ≤ a.hi := by exact_mod_cast ha
    unfold Interval.contains Interval.mid
    push_cast
    constructor <;> linarith
  refine ⟨?_, ?_, fun i j => ⟨(h.2.2 i j).1, mid _ (h.2.2 i j).2⟩⟩
  · intro i
    have hb := h.1 i
    simp only [sampled, midpointRealization, List.forall₂_map_right_iff, List.forall₂_same]
    intro s hs
    have v := List.forall_iff_forall_mem.mp hb s hs
    exact ⟨v.1, mid _ v.2⟩
  · intro i j
    have hm := h.2.1 i j
    simp only [midpointRealization, List.forall₂_map_right_iff, List.forall₂_same]
    intro m hs
    have v := List.forall_iff_forall_mem.mp hm m hs
    exact ⟨v.1, v.2.1, mid _ v.2.2.1, mid _ v.2.2.2⟩

def dosBox (b : Mesh p) (i : p) : Interval := weightBox b.halfWidth (b.bands i)
noncomputable def dos (b : Mesh p) (r : Realization p) (i : p) : ℝ :=
  match r.integratedDOS with
  | none => meshWeight b.halfWidth (b.bands i) (r.bands i)
  | some w => w i

theorem dos_enclosure (b : Mesh p) (r : Realization p) (h : b.matches r)
    (hw : 0 < b.halfWidth) (i : p) : (dosBox b i).contains (dos b r i) := by
  have hbands := h.1
  cases e : r.integratedDOS with
  | none =>
    simp only [e] at hbands
    simpa only [dos, dosBox, e] using weight_enclosure _ hw _ _ (hbands i)
  | some w =>
    simp only [e] at hbands
    simpa only [dos, dosBox, e] using hbands i

def transferSq (t : ℚ) (n m : Fin N) : ℚ × ℚ :=
  let v := Pairing.transfers t n m
  (v.1^2, v.2^2)

noncomputable def realTransferSq (t : ℝ) (n m : Fin N) : ℝ × ℝ :=
  ((t * ((frequencyIndex n : ℝ) - (frequencyIndex m : ℝ)))^2,
    (t * ((frequencyIndex n : ℝ) + (frequencyIndex m : ℝ)))^2)

@[simp] theorem realTransferSq_cast (t : ℚ) (n m : Fin N) :
    realTransferSq (t : ℝ) n m = (((transferSq t n m).1 : ℝ), ((transferSq t n m).2 : ℝ)) := by
  simp [realTransferSq, transferSq, Pairing.transfers]

theorem realTransferSq_le (t : ℝ) (n m : Fin N) :
    (realTransferSq t n m).1 ≤ (realTransferSq t n m).2 := by
  have hn : 0 ≤ (frequencyIndex n : ℝ) := by unfold frequencyIndex; push_cast; positivity
  have hm : 0 ≤ (frequencyIndex m : ℝ) := by unfold frequencyIndex; push_cast; positivity
  have hs : 0 ≤ 4 * t^2 * (frequencyIndex n : ℝ) * (frequencyIndex m : ℝ) := by positivity
  simp [realTransferSq]
  nlinarith only [hs]

theorem transferSq_le (t : ℚ) (n m : Fin N) :
    (transferSq t n m).1 ≤ (transferSq t n m).2 := by
  have hn : 0 ≤ frequencyIndex n := by unfold frequencyIndex; positivity
  have hm : 0 ≤ frequencyIndex m := by unfold frequencyIndex; positivity
  have hs : 0 ≤ 4 * t^2 * frequencyIndex n * frequencyIndex m := by positivity
  simp [transferSq, Pairing.transfers]
  nlinarith only [hs]

def kernelBox (b : Mesh p) (cutoff : ℕ) (t : ℚ) (a d : p × Fin N) : Interval :=
  let v := transferSq t a.2 d.2
  let ph := (phononEnvelope (b.modes a.1 d.1) v.1).add
    (phononEnvelope (b.modes a.1 d.1) v.2)
  if a.2.val < cutoff ∧ d.2.val < cutoff then ph.sub ((Interval.point 2).mulPos (b.coulomb a.1 d.1))
  else ph

noncomputable def meshKernel (r : Realization p) (cutoff : ℕ) (t : ℝ)
    (a d : p × Fin N) : ℝ :=
  let v := realTransferSq t a.2 d.2
  let ph := phononResponse (r.modes a.1 d.1) v.1 + phononResponse (r.modes a.1 d.1) v.2
  if a.2.val < cutoff ∧ d.2.val < cutoff then ph - 2 * r.coulomb a.1 d.1 else ph

theorem kernel_enclosure (b : Mesh p) (r : Realization p) (h : b.matches r)
    (cutoff : ℕ) (t : ℚ) (a d : p × Fin N) :
    (kernelBox b cutoff t a d).contains (meshKernel r cutoff t a d) := by
  have ha := phonon_enclosure _ _ (transferSq t a.2 d.2).1
    (by unfold transferSq; positivity) (h.2.1 a.1 d.1)
  have hd := phonon_enclosure _ _ (transferSq t a.2 d.2).2
    (by unfold transferSq; positivity) (h.2.1 a.1 d.1)
  unfold kernelBox meshKernel
  simp only [realTransferSq_cast]
  split
  · exact Interval.sub_contains (Interval.add_contains ha hd)
      (Interval.mul_contains (a := Interval.point 2) (by decide) (h.2.2 _ _).1
        (Interval.point_contains 2) (h.2.2 _ _).2)
  · exact Interval.add_contains ha hd

def metricBox [Fintype p] (b : Mesh p) (t : ℚ) (a : p × Fin N) : Interval :=
  let normal := Interval.sum fun d : p × Fin N =>
    let v := transferSq t a.2 d.2
    (dosBox b d.1).mulPos (((phononEnvelope (b.modes a.1 d.1) v.1).sub
      (phononEnvelope (b.modes a.1 d.1) v.2)).nonneg)
  ((Interval.point (frequencyIndex a.2)).add normal).divPos (dosBox b a.1)

noncomputable def meshMetric [Fintype p] (b : Mesh p) (r : Realization p) (t : ℝ) (a : p × Fin N) : ℝ :=
  let normal := ∑ d : p × Fin N,
    let v := realTransferSq t a.2 d.2
    dos b r d.1 * (phononResponse (r.modes a.1 d.1) v.1 -
      phononResponse (r.modes a.1 d.1) v.2)
  ((frequencyIndex a.2 : ℝ) + normal) / dos b r a.1

theorem metric_enclosure [Fintype p] (b : Mesh p) (r : Realization p) (h : b.matches r)
    (hw : 0 < b.halfWidth) (hd : ∀ i, 0 < (dosBox b i).lo) (t : ℚ) (a : p × Fin N) :
    (metricBox b t a).contains (meshMetric b r t a) := by
  have hwgt (i : p) : (dosBox b i).contains (dos b r i) := dos_enclosure b r h hw i
  unfold metricBox meshMetric
  simp only [realTransferSq_cast]
  apply Interval.div_contains _ (hd a.1) _ (hwgt a.1)
  · apply add_nonneg (by unfold frequencyIndex Interval.point; positivity)
    apply Finset.sum_nonneg
    intro d _
    apply mul_nonneg (hd d.1).le (le_max_left _ _)
  · apply Interval.add_contains (Interval.point_contains _)
    apply Interval.sum_contains
    intro d
    let v := transferSq t a.2 d.2
    have hq : 0 ≤ v.1 := by unfold v transferSq; positivity
    have hr := transferSq_le t a.2 d.2
    have ha := phonon_enclosure _ _ v.1 hq (h.2.1 a.1 d.1)
    have hb := phonon_enclosure _ _ v.2 (hq.trans hr) (h.2.1 a.1 d.1)
    have hn := phonon_decreases _ _ (by exact_mod_cast hq : 0 ≤ (v.1 : ℝ))
      (by exact_mod_cast hr : (v.1 : ℝ) ≤ (v.2 : ℝ)) (h.2.1 a.1 d.1)
    exact Interval.mul_contains (hd d.1).le (le_max_left _ _) (hwgt d.1)
      (Interval.nonneg_contains (Interval.sub_contains ha hb) (sub_nonneg.mpr hn))

end Grain.Pairing.Material
