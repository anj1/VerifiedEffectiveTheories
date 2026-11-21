import Grain.Energy

/-! Sparse rational vectors used to check matrix certificates against operator columns. -/

namespace Grain.Sparse

abbrev Vector (ι : Type) := List (ι × ℚ)

variable {ι : Type} [DecidableEq ι]

def entry (v : Vector ι) (i : ι) : ℚ :=
  (v.map fun (j, a) => if i = j then a else 0).sum

def dot (v : Vector ι) (x : ι → ℚ) : ℚ :=
  (v.map fun (i, a) => a * x i).sum

def scale (a : ℚ) (v : Vector ι) : Vector ι :=
  v.map fun (i, b) => (i, a * b)

def apply (columns : ι → Vector ι) (v : Vector ι) : Vector ι :=
  v.flatMap fun (i, a) => scale a (columns i)

def insert (i : ι) (a : ℚ) : Vector ι → Vector ι
  | [] => [(i, a)]
  | (j, b) :: v => if i = j then (j, a + b) :: v else (j, b) :: insert i a v

def compact (v : Vector ι) : Vector ι :=
  (v.foldr (fun (i, a) r => insert i a r) []).filter fun t => t.2 != 0

@[simp] theorem entry_nil (i : ι) : entry ([] : Vector ι) i = 0 := rfl

@[simp] theorem entry_cons (i j : ι) (a : ℚ) (v : Vector ι) :
    entry ((j, a) :: v) i = (if i = j then a else 0) + entry v i := rfl

@[simp] theorem entry_append (v w : Vector ι) (i : ι) :
    entry (v ++ w) i = entry v i + entry w i := by
  simp [entry, List.sum_append]

@[simp] theorem entry_scale (a : ℚ) (v : Vector ι) (i : ι) :
    entry (scale a v) i = a * entry v i := by
  induction v with
  | nil => simp [scale]
  | cons t v ih =>
    rcases t with ⟨j, b⟩
    change entry ((j, a * b) :: scale a v) i = _
    rw [entry_cons, entry_cons, ih, mul_add]
    split <;> simp_all

theorem entry_insert (i j : ι) (a : ℚ) (v : Vector ι) :
    entry (insert j a v) i = (if i = j then a else 0) + entry v i := by
  induction v with
  | nil => simp [insert]
  | cons t v ih =>
    rcases t with ⟨k, b⟩
    by_cases h : j = k
    · subst k
      simp only [insert, ite_true, entry_cons, ← add_assoc]
      split <;> simp_all
    · simp only [insert, h, ite_false, entry_cons, ih]
      abel

@[simp] theorem entry_compact (v : Vector ι) (i : ι) : entry (compact v) i = entry v i := by
  have hfilter (w : Vector ι) : entry (w.filter fun t => t.2 != 0) i = entry w i := by
    induction w with
    | nil => rfl
    | cons t w ih =>
      rcases t with ⟨j, a⟩
      by_cases h : a = 0 <;> simp [h, ih]
  unfold compact
  rw [hfilter]
  induction v with
  | nil => rfl
  | cons t v ih =>
    rcases t with ⟨j, a⟩
    simpa only [List.foldr_cons, entry_insert, entry_cons] using
      congrArg ((if i = j then a else 0) + ·) ih

variable [Fintype ι]

theorem dot_eq_sum (v : Vector ι) (x : ι → ℚ) :
    dot v x = ∑ i, entry v i * x i := by
  induction v with
  | nil => simp [dot]
  | cons t v ih =>
    rcases t with ⟨j, a⟩
    change a * x j + dot v x = _
    rw [ih]
    simp [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]

theorem entry_apply (columns : ι → Vector ι) (v : Vector ι) (i : ι) :
    entry (apply columns v) i = ∑ j, entry (columns j) i * entry v j := by
  have h : entry (apply columns v) i = dot v (fun j => entry (columns j) i) := by
    induction v with
    | nil => rfl
    | cons t v ih =>
      rcases t with ⟨j, a⟩
      simp only [apply, List.flatMap_cons, entry_append, entry_scale, dot, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]
  rw [h, dot_eq_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem sum_abs_entry (v : Vector ι) (w : ι → ℚ) (hw : ∀ i, 0 ≤ w i) :
    (∑ i, |entry v i| * w i) ≤ (v.map fun (j, a) => |a| * w j).sum := by
  induction v with
  | nil => simp
  | cons t v ih =>
    rcases t with ⟨j, a⟩
    calc
      _ ≤ ∑ i, ((if i = j then |a| else 0) + |entry v i|) * w i := by
        apply Finset.sum_le_sum
        intro i _
        rw [entry_cons]
        apply mul_le_mul_of_nonneg_right _ (hw i)
        simpa only [apply_ite abs, abs_zero] using abs_add_le (if i = j then a else 0) (entry v i)
      _ = |a| * w j + ∑ i, |entry v i| * w i := by
        simp [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
      _ ≤ _ := add_le_add_right ih _

omit [Fintype ι] in
theorem entry_filter (v : Vector ι) (p : ι → Bool) (i : ι) :
    entry (v.filter fun t => p t.1) i = if p i then entry v i else 0 := by
  induction v with
  | nil => simp
  | cons t v ih =>
    obtain ⟨j, a⟩ := t
    by_cases h : i = j
    · subst j; cases hp : p i <;> simp [hp, ih]
    · cases hp : p j <;> simp [hp, h, ih]

def offDiagonal (v : Vector ι) (i : ι) : Vector ι :=
  v.filter fun t => t.1 != i

def rowTest (v : Vector ι) (w : ι → ℚ) (l : ℚ) (i : ι) : Prop :=
  0 < w i ∧ l * w i + ((offDiagonal v i).map fun (j, a) => |a| * w j).sum ≤ entry v i * w i

instance (v : Vector ι) (w : ι → ℚ) (l : ℚ) (i : ι) : Decidable (rowTest v w l i) := by
  unfold rowTest
  infer_instance

set_option maxHeartbeats 600000 in
theorem lower_form (A : ι → ι → ℚ) (columns : ι → Vector ι) (w : ι → ℚ) (l : ℚ)
    (hA : ∀ i j, entry (columns j) i = A i j) (hs : ∀ i j, A i j = A j i)
    (h : ∀ i, rowTest (columns i) w l i) (x : ι → ℝ) :
    (l : ℝ) * normSq x ≤ form A x := by
  let C (i j : ι) := if i = j then A i i else -|A i j|
  have hrow (i : ι) : l * w i ≤ action C w i := by
    have hsum := sum_abs_entry (offDiagonal (columns i) i) w (fun j => (h j).1.le)
    have he (j : ι) : |entry (offDiagonal (columns i) i) j| * w j =
        if j = i then 0 else |A i j| * w j := by
      unfold offDiagonal
      rw [entry_filter _ (fun k => k != i), hA, hs j i]
      by_cases hj : j = i <;> simp [hj]
    simp_rw [he] at hsum
    have hd (j : ι) : C i j * w j =
        (if j = i then A i i * w i else 0) - (if j = i then 0 else |A i j| * w j) := by
      by_cases hj : j = i
      · subst j; simp [C]
      · simp [C, hj, Ne.symm hj]
    unfold action
    simp_rw [hd]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    have hw := (h i).2
    rw [hA i i] at hw
    linarith
  have lb := weighted_lower C w l (fun i j => by
    by_cases hij : i = j
    · subst j; rfl
    · simp [C, hij, Ne.symm hij, hs i j])
    (fun i j hij => by simp [C, hij]) (fun i => (h i).1) hrow (fun i => |x i|)
  have hf : form C (fun i => |x i|) ≤ form A x := by
    unfold form
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : i = j
    · subst j; simp [C]
    · simp only [C, hj, ite_false, Rat.cast_neg, Rat.cast_abs, ← abs_mul, neg_mul]
      exact neg_abs_le _
  simpa [normSq, sq_abs] using lb.trans hf

def quadratic (columns : ι → Vector ι) (v : Vector ι) : ℚ :=
  dot v (fun j => dot (columns j) (entry v))

theorem quadratic_eq (columns : ι → Vector ι) (v : Vector ι) :
    quadratic columns v = rayleighNumerator (fun i j => entry (columns j) i) (entry v) := by
  unfold quadratic rayleighNumerator action
  simp_rw [dot_eq_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem dot_self (v : Vector ι) : dot v (entry v) = rationalNormSq (entry v) := by
  simp [dot_eq_sum, rationalNormSq, pow_two]

/-- Subtract a positive Gram part when absolute row bounds alone are too wide. -/
def subtractSquares (columns : ι → Vector ι) (terms : List (ℚ × Vector ι))
    (j : ι) : Vector ι :=
  match terms with
  | [] => columns j
  | _ => compact (columns j ++ terms.flatMap fun (a, v) =>
      let b := entry v j
      if b = 0 then [] else scale (-(a * b)) v)

private def squareMatrix (terms : List (ℚ × Vector ι)) (i j : ι) : ℚ :=
  (terms.map fun (a, v) => a * entry v j * entry v i).sum

omit [Fintype ι] in
private theorem squareMatrix_cons (a : ℚ) (v : Vector ι) (vs : List (ℚ × Vector ι)) (i j : ι) :
    squareMatrix ((a,v) :: vs) i j = a * entry v j * entry v i + squareMatrix vs i j := rfl

omit [Fintype ι] in
private theorem entry_subtractSquares (columns : ι → Vector ι) (terms : List (ℚ × Vector ι))
    (i j : ι) : entry (subtractSquares columns terms j) i =
      entry (columns j) i - squareMatrix terms i j := by
  have h (vs : List (ℚ × Vector ι)) : entry (vs.flatMap fun (a,v) =>
      if entry v j = 0 then [] else scale (-(a * entry v j)) v) i =
        -squareMatrix vs i j := by
    induction vs with
    | nil => simp [squareMatrix]
    | cons t vs ih =>
      obtain ⟨a,v⟩ := t
      by_cases hz : entry v j = 0 <;>
        simp [List.flatMap_cons, hz, ih, squareMatrix_cons]; ring
  cases terms with
  | nil => simp [subtractSquares, squareMatrix]
  | cons t ts =>
    simp only [subtractSquares, entry_compact, entry_append, h, sub_eq_add_neg]

private theorem squareMatrix_nonneg (terms : List (ℚ × Vector ι))
    (h : ∀ t ∈ terms, 0 ≤ t.1) (x : ι → ℝ) : 0 ≤ form (squareMatrix terms) x := by
  induction terms with
  | nil => simp [squareMatrix, form]
  | cons t vs ih =>
    obtain ⟨a,v⟩ := t
    have ha : (0 : ℝ) ≤ a := by exact_mod_cast h _ (List.mem_cons_self ..)
    rw [show form (squareMatrix ((a,v) :: vs)) x =
        (a : ℝ) * (∑ i, (entry v i : ℝ) * x i)^2 + form (squareMatrix vs) x by
      simp only [form, squareMatrix_cons, Rat.cast_add, Rat.cast_mul, add_mul,
        Finset.sum_add_distrib, pow_two]
      congr 1
      simp only [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring]
    exact add_nonneg (by positivity) (ih fun u hu => h u (List.mem_cons_of_mem _ hu))

theorem lower_with_squares (A : ι → ι → ℚ) (columns : ι → Vector ι)
    (terms : List (ℚ × Vector ι)) (w : ι → ℚ) (l : ℚ)
    (hA : ∀ i j, entry (columns j) i = A i j) (hs : ∀ i j, A i j = A j i)
    (ht : ∀ t ∈ terms, 0 ≤ t.1)
    (h : ∀ i, rowTest (subtractSquares columns terms i) w l i) (x : ι → ℝ) :
    (l : ℝ) * normSq x ≤ form A x := by
  let B (i j : ι) := A i j - squareMatrix terms i j
  have symm (i j : ι) : B i j = B j i := by
    simp [B, hs i j, squareMatrix, mul_right_comm]
  have hb := lower_form B (subtractSquares columns terms) w l
    (by intro i j; rw [entry_subtractSquares, hA]) symm h x
  have hpos := squareMatrix_nonneg terms ht x
  change _ ≤ form (fun i j => A i j - squareMatrix terms i j) x at hb
  rw [form_sub] at hb
  linarith

def absSum (v : Vector ι) : ℚ := (v.map fun t => |t.2|).sum

omit [DecidableEq ι] [Fintype ι] in
theorem absSum_nonneg (v : Vector ι) : 0 ≤ absSum v := by
  induction v with
  | nil => rfl
  | cons t vs ih => exact add_nonneg (abs_nonneg _) ih

omit [DecidableEq ι] [Fintype ι] in
@[simp] theorem absSum_append (v w : Vector ι) :
    absSum (v ++ w) = absSum v + absSum w := by simp [absSum, List.sum_append]

omit [DecidableEq ι] [Fintype ι] in
@[simp] theorem absSum_scale (a : ℚ) (v : Vector ι) :
    absSum (scale a v) = |a| * absSum v := by
  induction v with
  | nil => simp [absSum, scale]
  | cons t vs ih =>
    obtain ⟨i,b⟩ := t
    change |a*b| + absSum (scale a vs) = |a| * (|b| + absSum vs)
    rw [abs_mul, ih, mul_add]

omit [DecidableEq ι] [Fintype ι] in
theorem absSum_flatMap {α : Type} (f : α → Vector ι) (s : List α) :
    absSum (s.flatMap f) = (s.map (fun a => absSum (f a))).sum := by
  induction s with
  | nil => rfl
  | cons a s ih => simp [ih]

omit [DecidableEq ι] [Fintype ι] in
theorem absSum_apply (columns : ι → Vector ι) (v : Vector ι) (b : ℚ)
    (h : ∀ i, absSum (columns i) ≤ b) :
    absSum (apply columns v) ≤ b * absSum v := by
  induction v with
  | nil => simp [absSum, apply]
  | cons t vs ih =>
    obtain ⟨i,a⟩ := t
    simp only [apply, List.flatMap_cons, absSum_append, absSum_scale] at ih ⊢
    change |a| * absSum (columns i) + absSum (List.flatMap _ vs) ≤ b * (|a| + absSum vs)
    rw [mul_add, mul_comm b |a|]
    exact add_le_add (mul_le_mul_of_nonneg_left (h i) (abs_nonneg _)) ih

omit [DecidableEq ι] [Fintype ι] in
theorem absSum_filter (v : Vector ι) (p : ι → Bool) :
    absSum (v.filter fun t => p t.1) ≤ absSum v := by
  induction v with
  | nil => rfl
  | cons t vs ih =>
    cases h : p t.1 <;> simp [h, absSum] at ih ⊢
    · linarith only [ih, abs_nonneg t.2]
    · exact ih

omit [Fintype ι] in
theorem absSum_compact (v : Vector ι) : absSum (compact v) ≤ absSum v := by
  have hi (i : ι) (a : ℚ) (vs : Vector ι) :
      absSum (insert i a vs) ≤ |a| + absSum vs := by
    induction vs with
    | nil => simp [insert, absSum]
    | cons t vs ih =>
      obtain ⟨j,b⟩ := t
      by_cases h : i = j
      · subst j
        simp [insert, absSum]
        linarith [abs_add_le a b]
      · simp [insert, h, absSum] at ih ⊢
        linarith
  have hf (vs : Vector ι) : absSum (vs.filter fun t => t.2 != 0) ≤ absSum vs := by
    induction vs with
    | nil => rfl
    | cons t vs ih =>
      by_cases h : t.2 = 0 <;> simpa [h, absSum] using ih
  unfold compact
  apply (hf _).trans
  induction v with
  | nil => rfl
  | cons t vs ih =>
    obtain ⟨i,a⟩ := t
    change absSum (insert i a _) ≤ |a| + absSum vs
    exact (hi i a _).trans (add_le_add (le_refl |a|) ih)

omit [Fintype ι] in
theorem rowTest_kinetic (v : Vector ι) (w : ι → ℚ) (l k b : ℚ) (i : ι)
    (hw : 0 < w i) (hmax : ∀ j, w j ≤ w i) (hb : absSum v ≤ b) (hl : l + b ≤ k) :
    rowTest ((i,k) :: v) w l i := by
  have hbudget : ((offDiagonal v i).map fun (j,a) => |a| * w j).sum
      - entry v i * w i ≤ absSum v * w i := by
    clear hb
    induction v with
    | nil => simp [offDiagonal, absSum]
    | cons t vs ih =>
      obtain ⟨j,a⟩ := t
      by_cases hij : i = j
      · subst j
        simp [offDiagonal, absSum, add_mul] at ih ⊢
        linarith only [ih, mul_le_mul_of_nonneg_right (neg_le_abs a) hw.le]
      · simp [offDiagonal, hij, Ne.symm hij, absSum, add_mul] at ih ⊢
        linarith only [ih, mul_le_mul_of_nonneg_left (hmax j) (abs_nonneg a)]
  refine ⟨hw, ?_⟩
  simp only [offDiagonal, List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ite_false,
    entry_cons, ite_true, add_mul]
  unfold offDiagonal at hbudget
  have hk : l + absSum v ≤ k := by linarith only [hb, hl]
  linarith only [hbudget, mul_le_mul_of_nonneg_right hk hw.le]

end Grain.Sparse
