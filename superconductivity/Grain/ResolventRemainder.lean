import Grain.Energy

/-! A finite discarded-block estimate in the maximum norm. -/
namespace Grain.ResolventRemainder

open scoped BigOperators

def action {ι : Type} [Fintype ι] (T : ι → ι → ℝ) (x : ι → ℝ) (i : ι) :=
  ∑ j, T i j * x j

private theorem action_bound {ι : Type} [Fintype ι] (T : ι → ι → ℝ) (x : ι → ℝ)
    (i : ι) {B X : ℝ} (hB : ∑ j, |T i j| ≤ B) (hX : 0 ≤ X)
    (hx : ∀ i, |x i| ≤ X) : |action T x i| ≤ B * X := by
  unfold action
  calc
    _ ≤ ∑ j, |T i j * x j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |T i j| * X := by
      simp only [abs_mul]
      exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hx j) (abs_nonneg _)
    _ = (∑ j, |T i j|) * X := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hB hX

/-- A bound for any solution of a diagonally dominant discarded equation. -/
theorem discarded_bound {ι : Type} [Fintype ι] (D : ι → ℝ) (T : ι → ι → ℝ)
    (x b : ι → ℝ) {gap g B shift R : ℝ} (hg : 0 ≤ g) (hshift : shift ≤ 0)
    (hgap : g * B < gap) (hD : ∀ i, gap ≤ D i) (hB : ∀ i, ∑ j, |T i j| ≤ B)
    (hb : ∀ i, |b i| ≤ R) (he : ∀ i, (D i - shift) * x i = b i + g * action T x i) :
    ∀ i, |x i| ≤ R / (gap - g * B) := by
  intro i
  classical
  obtain ⟨k, _, hk⟩ := Finset.exists_max_image Finset.univ (fun j => |x j|)
    ⟨i, Finset.mem_univ i⟩
  have hx (j : ι) : |x j| ≤ |x k| := hk j (Finset.mem_univ j)
  have hB0 : 0 ≤ B := (Finset.sum_nonneg fun j _ => abs_nonneg (T k j)).trans (hB k)
  have hp : 0 < gap - g * B := sub_pos.mpr hgap
  have hd : 0 ≤ D k - shift := by linarith [hD k, mul_nonneg hg hB0]
  have ht : |g * action T x k| ≤ g * (B * |x k|) := by
    rw [abs_mul, abs_of_nonneg hg]
    exact mul_le_mul_of_nonneg_left (action_bound T x k (hB k) (abs_nonneg _) hx) hg
  have h := (abs_add_le (b k) (g * action T x k)).trans (add_le_add (hb k) ht)
  rw [← he k, abs_mul, abs_of_nonneg hd] at h
  apply (hx i).trans
  apply (le_div_iff₀ hp).2
  nlinarith [mul_le_mul_of_nonneg_right (show gap ≤ D k - shift by linarith [hD k])
    (abs_nonneg (x k))]

def dot {ι : Type} [Fintype ι] (v x : ι → ℝ) := ∑ j, v j * x j

private theorem dot_bound {ι : Type} [Fintype ι] (v x : ι → ℝ) {V X : ℝ}
    (hV : ∑ j, |v j| ≤ V) (hX : 0 ≤ X) (hx : ∀ i, |x i| ≤ X) :
    |dot v x| ≤ V * X := by
  classical
  rcases isEmpty_or_nonempty ι with hempty | ⟨⟨i⟩⟩
  · let := hempty
    have hV0 : 0 ≤ V := by simpa using hV
    simpa [dot] using mul_nonneg hV0 hX
  · exact action_bound (fun (_ : ι) => v) x i hV hX hx

/-- Absolute sector error budget for a positive discarded gap. -/
noncomputable def budget (gap g B V : ℝ) : ℝ :=
  let U := 1 / gap
  let W := B * U / gap
  let Y := 1 / (gap - g * B)
  g ^ 4 * V * (B * W + V * Y * (U + g * W)) / (gap - g * B)

/-- The first two resolvent terms and a bound on the exact energy shift left over.
The head equation and the discarded equations are written in components, with
the head amplitude normalized to one (and the tail amplitude scaled by g). -/
theorem sector_remainder {ι : Type} [Fintype ι] (D : ι → ℝ) (T : ι → ι → ℝ)
    (v y : ι → ℝ) {gap g B V shift : ℝ}
    (hg : 0 ≤ g) (hshift : shift ≤ 0) (hgap : 0 < gap) (hsmall : g * B < gap)
    (hB0 : 0 ≤ B) (hV0 : 0 ≤ V)
    (hD : ∀ i, gap ≤ D i) (hB : ∀ i, ∑ j, |T i j| ≤ B)
    (hv : ∀ i, |v i| ≤ 1) (hV : ∑ j, |v j| ≤ V)
    (htail : ∀ i, (D i - shift) * y i = v i + g * action T y i)
    (hhead : shift = -g ^ 2 * dot v y) :
    let u := fun i => v i / D i
    let w := fun i => action T u i / D i
    |shift - (-g ^ 2 * dot v u - g ^ 3 * dot v w)| ≤ budget gap g B V := by
  dsimp only [budget]
  let u := fun i => v i / D i
  let w := fun i => action T u i / D i
  let U := 1 / gap
  let W := B * U / gap
  let Y := 1 / (gap - g * B)
  have hp : 0 < gap - g * B := sub_pos.mpr hsmall
  have hU : 0 ≤ U := by positivity
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  have hu (i : ι) : |u i| ≤ U := by
    dsimp [u, U]
    rw [abs_div, abs_of_pos (hgap.trans_le (hD i))]
    exact div_le_div₀ (by norm_num) (hv i) hgap (hD i)
  have hw (i : ι) : |w i| ≤ W := by
    dsimp [w, W]
    rw [abs_div, abs_of_pos (hgap.trans_le (hD i))]
    exact div_le_div₀ (mul_nonneg hB0 hU) (action_bound T u i (hB i) hU hu) hgap (hD i)
  have hy : ∀ i, |y i| ≤ Y := discarded_bound D T y v hg hshift hsmall hD hB hv htail
  have hl : |shift| ≤ g ^ 2 * (V * Y) := by
    rw [hhead, abs_mul, abs_neg, abs_of_nonneg (sq_nonneg g)]
    exact mul_le_mul_of_nonneg_left (dot_bound v y hV hY hy) (sq_nonneg g)
  let e := fun i => y i - (u i + g * w i)
  let b := fun i => g ^ 2 * action T w i + shift * (u i + g * w i)
  let R := g ^ 2 * (B * W + V * Y * (U + g * W))
  have he (i : ι) : (D i - shift) * e i = b i + g * action T e i := by
    have hui : D i * u i = v i := by dsimp [u]; field_simp [(hgap.trans_le (hD i)).ne']
    have hwi : D i * w i = action T u i := by dsimp [w]; field_simp [(hgap.trans_le (hD i)).ne']
    have hact : action T e i = action T y i - (action T u i + g * action T w i) := by
      simp [action, e, mul_sub, mul_add, mul_left_comm _ g, Finset.sum_sub_distrib,
        Finset.sum_add_distrib, Finset.mul_sum]
    rw [hact]
    dsimp [e, b]
    linear_combination htail i - hui - g * hwi
  have hb (i : ι) : |b i| ≤ R := by
    have hsum : |u i + g * w i| ≤ U + g * W := by
      apply (abs_add_le _ _).trans
      rw [abs_mul, abs_of_nonneg hg]
      exact add_le_add (hu i) (mul_le_mul_of_nonneg_left (hw i) hg)
    calc
      _ ≤ g ^ 2 * |action T w i| + |shift| * |u i + g * w i| := by
        have h := abs_add_le (g ^ 2 * action T w i) (shift * (u i + g * w i))
        rw [abs_mul, abs_of_nonneg (sq_nonneg g), abs_mul] at h
        exact h
      _ ≤ g ^ 2 * (B * W) + (g ^ 2 * (V * Y)) * (U + g * W) := by
        exact add_le_add (mul_le_mul_of_nonneg_left (action_bound T w i (hB i) hW hw) (sq_nonneg g))
          (mul_le_mul hl hsum (abs_nonneg _) (by positivity))
      _ = R := by dsimp [R]; ring
  have he' := discarded_bound D T e b hg hshift hsmall hD hB hb he
  have hR : 0 ≤ R / (gap - g * B) := by dsimp [R]; positivity
  have hdot : dot v e = dot v y - (dot v u + g * dot v w) := by
    simp [dot, e, mul_sub, mul_add, mul_left_comm _ g, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, Finset.mul_sum]
  change |shift - (-g ^ 2 * dot v u - g ^ 3 * dot v w)| ≤ _
  rw [show shift - (-g ^ 2 * dot v u - g ^ 3 * dot v w) = -g ^ 2 * dot v e by
    rw [hhead, hdot]; ring, abs_mul, abs_neg, abs_of_nonneg (sq_nonneg g)]
  convert mul_le_mul_of_nonneg_left (dot_bound v e hV hR he') (sq_nonneg g) using 1
  dsimp [R, U, W, Y]
  ring

/-- A nonzero eigenvector at or below the reference energy can be normalized
at the head. Strict diagonal dominance rules out a vector supported in the tail. -/
theorem normalize_eigenvector {ι : Type} [Fintype ι] (D : ι → ℝ) (T : ι → ι → ℝ)
    (v x : ι → ℝ) {gap g B shift head : ℝ}
    (hg : 0 < g) (hs : shift ≤ 0) (hgap : g * B < gap)
    (hD : ∀ i, gap ≤ D i) (hB : ∀ i, ∑ j, |T i j| ≤ B)
    (hne : head ≠ 0 ∨ x ≠ 0)
    (ht : ∀ i, (D i - shift) * x i = g * (head * v i + action T x i))
    (hh : shift * head = -g * dot v x) :
    ∃ y : ι → ℝ, (∀ i, (D i - shift) * y i = v i + g * action T y i) ∧
      shift = -g ^ 2 * dot v y := by
  have ha : head ≠ 0 := by
    intro h
    have ht0 (i : ι) : (D i - shift) * x i = (0 : ι → ℝ) i + g * action T x i := by
      simpa [h] using ht i
    have hx := discarded_bound D T x 0 hg.le hs hgap hD hB (R := 0) (by simp) ht0
    have hx0 : x = 0 := by
      funext i
      simpa using hx i
    exact hne.elim (fun hn => hn h) (fun hn => hn hx0)
  let y := fun i => x i / (g * head)
  refine ⟨y, ?_, ?_⟩
  · intro i
    have hact : action T y i = action T x i / (g * head) := by
      simp [action, y, mul_div_assoc, Finset.sum_div]
    rw [hact]
    dsimp [y]
    field_simp [hg.ne', ha]
    linear_combination ht i
  · have hd : dot v y = dot v x / (g * head) := by
      simp [dot, y, mul_div_assoc, Finset.sum_div]
    rw [hd]
    field_simp [hg.ne', ha]
    linear_combination hh

/-- Compare an eigenvalue of the head-and-tail Hamiltonian with its cubic truncation. -/
theorem eigenvalue_remainder {ι : Type} [Fintype ι] (D : ι → ℝ) (T : ι → ι → ℝ)
    (v x : ι → ℝ) {gap g B V shift head : ℝ}
    (hg : 0 < g) (hs : shift ≤ 0) (hgap : 0 < gap) (hsmall : g * B < gap)
    (hB0 : 0 ≤ B) (hV0 : 0 ≤ V) (hD : ∀ i, gap ≤ D i)
    (hB : ∀ i, ∑ j, |T i j| ≤ B) (hv : ∀ i, |v i| ≤ 1) (hV : ∑ j, |v j| ≤ V)
    (hne : head ≠ 0 ∨ x ≠ 0)
    (ht : ∀ i, (D i - shift) * x i = g * (head * v i + action T x i))
    (hh : shift * head = -g * dot v x) :
    let u := fun i => v i / D i
    let w := fun i => action T u i / D i
    |shift - (-g ^ 2 * dot v u - g ^ 3 * dot v w)| ≤ budget gap g B V := by
  obtain ⟨y, ht', hh'⟩ := normalize_eigenvector D T v x hg hs hsmall hD hB hne ht hh
  exact sector_remainder D T v y hg.le hs hgap hsmall hB0 hV0 hD hB hv hV ht' hh'

/-- The odd sector has weight one and the even sectors each have weight one half. -/
theorem parity_error (exactE cubicE : Fin 3 → ℝ) {R : ℝ}
    (h : ∀ i, |exactE i - cubicE i| ≤ R) :
    |(exactE 1 - (exactE 0 + exactE 2) / 2) - (cubicE 1 - (cubicE 0 + cubicE 2) / 2)|
      ≤ 2 * R := by
  have h₀ := abs_le.mp (h 0)
  have h₁ := abs_le.mp (h 1)
  have h₂ := abs_le.mp (h 2)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The cubic resolvent coefficient is the sum over ordered closed three-hop routes. -/
theorem cubic_loop_expansion {ι : Type} [Fintype ι] (D : ι → ℝ) (T : ι → ι → ℝ)
    (v : ι → ℝ) :
    dot v (fun i => action T (fun j => v j / D j) i / D i) =
      ∑ i, ∑ j, (v i / D i) * T i j * (v j / D j) := by
  unfold dot action
  apply Finset.sum_congr rfl
  intro i _
  change v i * ((∑ j, T i j * (v j / D j)) / D i) = _
  rw [div_eq_mul_inv, ← mul_assoc, mul_right_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp [div_eq_mul_inv, mul_assoc]

end Grain.ResolventRemainder
