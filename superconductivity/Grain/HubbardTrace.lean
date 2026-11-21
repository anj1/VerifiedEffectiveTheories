import Grain.HubbardChannels
import Grain.ThermalTrace

/-! Sparse integer evaluation of the Taylor trace. The lists of blocks and
sparse columns are witnesses. The checker ties them to the signed operators. -/

namespace Grain.HubbardChannels

open Matrix

noncomputable def hamiltonian (mask : Fin 8) (field : Bool) (d : ℕ) : Matrix State State ℝ :=
  fun i j => -(entry mask field i j : ℝ) / d

structure Block where
  states : List State
  columns : List (List (ℕ × ℤ))
  deriving Inhabited

def blockValid (mask : Fin 8) (field : Bool) (b : Block) : Prop :=
  b.states.Nodup ∧
  (b.states.map fun j => (column mask field j).map fun (i, v) => (b.states.idxOf i, -v))
    = b.columns ∧
  ∀ j ∈ b.states, ∀ row ∈ column mask field j, row.1 ∈ b.states

instance (mask : Fin 8) (field : Bool) (b : Block) : Decidable (blockValid mask field b) := by
  unfold blockValid
  infer_instance

def localAction (b : Block) (x : List ℤ) : List ℤ :=
  b.columns.map fun col => (col.map fun (i, v) => v * x[i]?.getD 0).sum

/-- Taylor numerator accumulation in ascending order. -/
def moments (b : Block) (d root : ℕ) : ℕ → List ℤ × ℤ × ℤ
  | 0 => ((List.range b.states.length).map fun i => if i = root then 1 else 0, 1, 1)
  | k+1 =>
    let (x, s, scale) := moments b d root k
    let y := localAction b x
    let ratio : ℤ := (d : ℤ) * (k + 1)
    (y, ratio * s + y[root]?.getD 0, ratio * scale)

def numerator (b : Block) (d n : ℕ) : ℤ :=
  ((List.range b.states.length).map fun root => (moments b d root n).2.1).sum

def denominator (d n : ℕ) : ℕ := d ^ n * n.factorial

private theorem sum_map_mul (f : State × ℤ → ℤ) (l : List (State × ℤ)) (a : ℤ) :
    a * (l.map f).sum = (l.map fun v => a * f v).sum := by
  induction l with
  | nil => simp
  | cons v l ih => simp [mul_add, ih]

private theorem entries_sum (mask : Fin 8) (field : Bool) (a : State) (f : State → ℤ) :
    (∑ i, f i * -(entry mask field i a)) =
      ((column mask field a).map fun (i, v) => -v * f i).sum := by
  let g (v : State × ℤ) (i : State) : ℤ := if v.1 = i then -v.2 * f i else 0
  have left : ∀ i, f i * -(entry mask field i a) =
      ((column mask field a).map fun v => g v i).sum := by
    intro i
    rw [mul_neg, ← neg_mul, entry, sum_map_mul]
    apply congrArg List.sum
    apply List.map_congr_left
    intro v _
    by_cases hv : v.1 = i
    · simp [g, hv, mul_comm]
    · simp [g, hv]
  simp_rw [left]
  clear left
  induction column mask field a with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]
    congr 1
    simp [g, eq_comm]

private theorem abs_entries_sum (mask : Fin 8) (field : Bool) (a : State) :
    (∑ i, |entry mask field i a|) ≤
      ((column mask field a).map fun (_, v) => (|v| : ℤ)).sum := by
  unfold entry
  induction column mask field a with
  | nil => simp
  | cons v l ih =>
    simp only [List.map_cons, List.sum_cons]
    calc
      _ ≤ ∑ i : State, (|(if v.1 = i then v.2 else 0)| +
          |(l.map fun v' => if v'.1 = i then v'.2 else 0).sum|) :=
          Finset.sum_le_sum fun _ _ => abs_add_le _ _
      _ ≤ _ := by
        rw [Finset.sum_add_distrib]
        simp_rw [apply_ite abs, abs_zero]
        have hv : (∑ i : State, if v.1 = i then |v.2| else 0) = |v.2| := by
          simp [eq_comm]
        rw [hv]
        exact add_le_add_right ih _

def integerMatrix (mask : Fin 8) (field : Bool) : Matrix State State ℤ :=
  fun i j => -entry mask field i j

private theorem get_idxOf (l : List State) (hl : l.Nodup) {i : ℕ} (hi : i < l.length) :
    l.idxOf l[i] = i := by
  have h := List.idxOf_lt_length_iff.mpr (List.getElem_mem hi)
  exact hl.getElem_inj_iff.mp (List.getElem_idxOf h)

private theorem localAction_at (mask : Fin 8) (field : Bool) (b : Block)
    (hb : blockValid mask field b) (x : List ℤ) (f : State → ℤ)
    (hx : ∀ (i : ℕ) (hi : i < b.states.length), x[i]?.getD 0 = f b.states[i])
    (j : ℕ) (hj : j < b.states.length) :
    (localAction b x)[j]?.getD 0 = (∑ i, f i * integerMatrix mask field i b.states[j]) := by
  simp only [integerMatrix]
  rw [entries_sum, localAction, ← hb.2.1,
    List.getElem?_map, List.getElem?_map, List.getElem?_eq_getElem hj]
  simp only [Option.map_some, Option.getD_some, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro v hv
  have hi : b.states.idxOf v.1 < b.states.length :=
    List.idxOf_lt_length_iff.mpr (hb.2.2 _ (List.getElem_mem hj) _ hv)
  change -v.2 * x[b.states.idxOf v.1]?.getD 0 = _
  rw [hx _ hi, List.getElem_idxOf hi]

private theorem moments_power (mask : Fin 8) (field : Bool) (b : Block)
    (hb : blockValid mask field b) (d root : ℕ) (hr : root < b.states.length) (k : ℕ) :
    ∀ (j : ℕ) (hj : j < b.states.length),
      (moments b d root k).1[j]?.getD 0 =
        (integerMatrix mask field ^ k) b.states[root] b.states[j] := by
  induction k with
  | zero =>
    intro j hj
    simp [moments, List.getElem?_map, List.getElem?_range hj, Matrix.one_apply,
      hb.1.getElem_inj_iff, eq_comm]
  | succ k ih =>
    intro j hj
    rw [pow_succ, Matrix.mul_apply]
    exact localAction_at mask field b hb _ _ ih j hj

private theorem hamiltonian_power (mask : Fin 8) (field : Bool) (d k : ℕ) (i j : State) :
    (hamiltonian mask field d ^ k) i j =
      ((integerMatrix mask field ^ k) i j : ℝ) / (d : ℝ)^k := by
  have hm : hamiltonian mask field d =
      (d : ℝ)⁻¹ • (integerMatrix mask field).map (Int.castRingHom ℝ) := by
    ext i j
    simp [hamiltonian, integerMatrix, div_eq_mul_inv, mul_comm]
  rw [hm, smul_pow, ← Matrix.map_pow]
  simp [inv_pow, div_eq_mul_inv, mul_comm]

private theorem moment_sum (mask : Fin 8) (field : Bool) (b : Block)
    (hb : blockValid mask field b) (d root : ℕ) (hd : 0 < d) (hr : root < b.states.length) (n : ℕ) :
    ((moments b d root n).2.1 : ℝ) =
      (denominator d n : ℝ) * ∑ k ∈ Finset.range (n+1),
        (hamiltonian mask field d ^ k) b.states[root] b.states[root] / (k.factorial : ℝ) := by
  have hd' : (d : ℝ) ≠ 0 := by positivity
  induction n with
  | zero => simp [moments, denominator]
  | succ n ih =>
    have hp := moments_power mask field b hb d root hr (n+1) root hr
    change (localAction b (moments b d root n).1)[root]?.getD 0 = _ at hp
    rw [Finset.sum_range_succ, hamiltonian_power, mul_add]
    simp only [moments, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_one]
    rw [hp, ih]
    have hden : (denominator d (n+1) : ℝ) =
        (d : ℝ) * ((n : ℝ)+1) * (denominator d n : ℝ) := by
      simp [denominator, pow_succ, Nat.factorial_succ]
      ring
    have hc (x : ℝ) :
        (denominator d (n+1) : ℝ) * (x / (d : ℝ)^(n+1) / ((n+1).factorial : ℝ)) = x := by
      simp only [denominator, Nat.cast_mul, Nat.cast_pow]
      have hn : (((n+1).factorial : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp
    rw [hc, hden]
    ring

def coverage (blocks : List Block) : Prop :=
  (blocks.flatMap Block.states).Nodup ∧ ∀ a : State, a ∈ blocks.flatMap Block.states

instance (blocks : List Block) : Decidable (coverage blocks) := by
  unfold coverage
  infer_instance

private theorem map_range_get (l : List State) (f : State → ℝ) :
    ((List.range l.length).map fun i => f (l[i]?.getD 0)) = l.map f := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have hi' : i < l.length := by simpa using hi
    simp [List.getElem?_eq_getElem hi']

private theorem numerator_eq (mask : Fin 8) (field : Bool) (b : Block)
    (hb : blockValid mask field b) (d : ℕ) (hd : 0 < d) (n : ℕ) :
    (numerator b d n : ℝ) =
      (b.states.map fun i => (denominator d n : ℝ) * ∑ k ∈ Finset.range (n+1),
        (hamiltonian mask field d ^ k) i i / (k.factorial : ℝ)).sum := by
  unfold numerator
  rw [Int.cast_list_sum, List.map_map, ← map_range_get]
  apply congrArg List.sum
  apply List.map_congr_left
  intro root hr
  have h := List.mem_range.mp hr
  rw [List.getElem?_eq_getElem h, Option.getD_some]
  exact moment_sum mask field b hb d root hd h n

def total (blocks : List Block) (d n : ℕ) : ℤ :=
  (blocks.map fun b => numerator b d n).sum

theorem total_append (a b : List Block) (d n : ℕ) :
    total (a ++ b) d n = total a d n + total b d n := by
  simp [total, List.sum_append]

theorem taylor_eq (mask : Fin 8) (field : Bool) (blocks : List Block)
    (hv : ∀ b ∈ blocks, blockValid mask field b) (hc : coverage blocks)
    (d : ℕ) (hd : 0 < d) (n : ℕ) :
    (total blocks d n : ℝ) =
      (denominator d n : ℝ) * ∑ k ∈ Finset.range (n+1),
        (hamiltonian mask field d ^ k).trace / (k.factorial : ℝ) := by
  unfold total
  rw [Int.cast_list_sum, List.map_map]
  let f (i : State) := (denominator d n : ℝ) * ∑ k ∈ Finset.range (n+1),
    (hamiltonian mask field d ^ k) i i / (k.factorial : ℝ)
  have h : (blocks.map fun b => (numerator b d n : ℝ)) =
      (blocks.map fun b => (b.states.map f).sum) :=
    List.map_congr_left fun b hb => numerator_eq mask field b (hv b hb) d hd n
  simp only [Function.comp_def]
  rw [h]
  have hall : (blocks.flatMap Block.states).toFinset = Finset.univ := by
    ext i
    simp [hc.2 i]
  have hs :
      ∑ i, f i = (List.map (fun b => (List.map f b.states).sum) blocks).sum := by
    rw [← hall, List.sum_toFinset f hc.1, List.map_flatMap]
    clear hv hc h hall
    induction blocks with
    | nil => simp
    | cons b l ih => simp [List.sum_append, ih]
  rw [← hs]
  dsimp [f]
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [Matrix.trace, Finset.sum_div]
  rfl

theorem column_norm (mask : Fin 8) (field : Bool) (d : ℕ) (hd : 0 < d) (r : ℕ)
    (h : ∀ a : State, ((column mask field a).map fun (_, v) => (|v| : ℤ)).sum ≤
      (r : ℤ) * d) (a : State) :
    ∑ i, |(hamiltonian mask field d).transpose a i| ≤ r := by
  simp only [Matrix.transpose_apply, hamiltonian, abs_div, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ d)]
  rw [← Finset.sum_div]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < d)).2
  have hi := (abs_entries_sum mask field a).trans (h a)
  exact_mod_cast hi

end Grain.HubbardChannels

namespace Grain.HubbardChannels

open Matrix ThermalTrace

def traceCenter (value : ℤ) (d n : ℕ) : ℚ := (value : ℚ) / denominator d n

def traceError (r n : ℕ) : ℚ := 512 * (r : ℚ)^(n+1) / ((n+1).factorial : ℚ)

theorem partition_checked (mask : Fin 8) (field : Bool) (blocks : List Block)
    (hv : ∀ b ∈ blocks, blockValid mask field b) (hc : coverage blocks)
    (d : ℕ) (hd : 0 < d) (n r : ℕ)
    (hr : 2*r ≤ n+2)
    (hnorm : ∀ a : State, ((column mask field a).map fun (_, v) => (|v| : ℤ)).sum ≤
      (r : ℤ) * d)
    (value : ℤ) (he : total blocks d n = value) :
    ((traceCenter value d n - traceError r n : ℚ) : ℝ) ≤ partition (hamiltonian mask field d) ∧
    partition (hamiltonian mask field d) ≤ ((traceCenter value d n + traceError r n : ℚ) : ℝ) := by
  let A := hamiltonian mask field d
  have ht := partition_enclosure A.transpose (r := (r : ℝ)) (by positivity)
    (column_norm mask field d hd r hnorm) (n + 1) (by
      apply (div_le_iff₀ (by positivity)).2
      have h : (2 : ℝ) * r ≤ (n : ℝ) + 2 := by exact_mod_cast hr
      push_cast
      linarith)
  have eq : (fun k : ℕ => (A.transpose ^ k).trace / (k.factorial : ℝ)) =
      (fun k : ℕ => (A ^ k).trace / (k.factorial : ℝ)) := by
    funext k
    rw [← Matrix.transpose_pow, Matrix.trace_transpose]
  unfold partition at ht ⊢
  simp only [eq, ← Matrix.transpose_pow, Matrix.trace_transpose] at ht
  have hy := taylor_eq mask field blocks hv hc d hd n
  rw [he] at hy
  have hs : (traceCenter value d n : ℝ) =
      ∑ k ∈ Finset.range (n+1), (A ^ k).trace / (k.factorial : ℝ) := by
    simp only [traceCenter, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
    apply (div_eq_iff (by unfold denominator; positivity)).2
    rw [mul_comm]
    exact hy
  rw [← hs] at ht
  norm_num [Fintype.card_fin] at ht
  push_cast
  simp only [traceError, Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast, Rat.cast_ofNat]
  obtain ⟨hl, hu⟩ := abs_le.mp ht
  constructor <;> linarith

noncomputable def benchmarkResponse (mask : Fin 8) (d : ℕ) : ℝ :=
  200 * ((d : ℝ) / 40) * Real.log
    (partition (hamiltonian mask true d) / partition (hamiltonian mask false d))

def endpointArg (d : ℕ) (x : ℚ) : ℚ := x / (5 * d)

def responseTest (d : ℕ) (l u a b c e : ℚ) : Prop :=
  0 < a ∧ 0 ≤ endpointArg d l ∧ endpointArg d l ≤ 1 ∧
    0 ≤ endpointArg d u ∧ endpointArg d u ≤ 1 ∧
    BCS.expUpper (endpointArg d l) 12 1 * b ≤ c ∧
    e ≤ BCS.expLower (endpointArg d u) 12 1 * a

instance (d : ℕ) (l u a b c e : ℚ) : Decidable (responseTest d l u a b c e) := by
  unfold responseTest
  infer_instance

theorem response_checked (mask : Fin 8) (d : ℕ) (hd : 0 < d) (l u a b c e : ℚ)
    (h0 : (a : ℝ) ≤ partition (hamiltonian mask false d) ∧
      partition (hamiltonian mask false d) ≤ (b : ℝ))
    (h1 : (c : ℝ) ≤ partition (hamiltonian mask true d) ∧
      partition (hamiltonian mask true d) ≤ (e : ℝ))
    (h : responseTest d l u a b c e) :
    (l : ℝ) ≤ benchmarkResponse mask d ∧ benchmarkResponse mask d ≤ (u : ℝ) := by
  obtain ⟨ha, hl, hl', hu, hu', hc, he⟩ := h
  have hb : 0 ≤ (b : ℝ) := (by exact_mod_cast ha.le : 0 ≤ (a : ℝ)).trans (h0.1.trans h0.2)
  have eq (x : ℚ) : (endpointArg d x : ℝ) = (x : ℝ) / (200 * ((d : ℝ)/40)) := by
    push_cast [endpointArg]
    ring_nf
  have hlow := (BCS.exp_enclosure _ 12 1 hl (by decide) (by decide) (by simpa using hl')).2.2
  have hupp := (BCS.exp_enclosure _ 12 1 hu (by decide) (by decide) (by simpa using hu')).2.1
  unfold benchmarkResponse
  apply response_enclosure (by positivity) (by exact_mod_cast ha) h0 h1
  · rw [← eq]
    exact (mul_le_mul_of_nonneg_right hlow hb).trans (by exact_mod_cast hc)
  · rw [← eq]
    exact (show (e : ℝ) ≤ (BCS.expLower (endpointArg d u) 12 1 : ℝ) * a by
        exact_mod_cast he).trans (mul_le_mul_of_nonneg_right hupp (by exact_mod_cast ha.le))

end Grain.HubbardChannels
