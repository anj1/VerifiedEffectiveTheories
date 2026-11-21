import Grain.HubbardTrace

/-! Checkpoints for the larger sparse thermal blocks. Each checkpoint
carries the exact vector and accumulated integer Taylor numerator. -/

namespace Grain.HubbardChannels

def advance (b : Block) (d root offset : ℕ) :
    ℕ → (List ℤ × ℤ × ℤ) → (List ℤ × ℤ × ℤ)
  | 0, start => start
  | n+1, start =>
    let (x, s, scale) := advance b d root offset n start
    let y := localAction b x
    let ratio : ℤ := (d : ℤ) * (offset + n + 1 : ℕ)
    (y, ratio * s + y[root]?.getD 0, ratio * scale)

theorem moments_checkpoint (b : Block) (d root offset steps : ℕ) :
    moments b d root (offset + steps) =
      advance b d root offset steps (moments b d root offset) := by
  induction steps with
  | zero => rfl
  | succ n ih =>
    simp only [Nat.add_succ, moments, advance]
    change moments b d root (offset.add n) =
      advance b d root offset n (moments b d root offset) at ih
    rw [ih]
    have h : ((offset.add n : ℕ) : ℤ) = (offset : ℤ) + n := Int.natCast_add offset n
    rw [h]
    push_cast <;> rfl

private theorem sum_of_diagonal {f : ℕ → ℤ} {indices : List ℕ} {values : List ℤ}
    (h : List.Forall₂ (fun i v => f i = v) indices values) :
    (indices.map f).sum = values.sum := by
  induction h with
  | nil => rfl
  | cons h _ ih => simp only [List.map_cons, List.sum_cons, h, ih]

theorem singleton_trace (b : Block) (d n : ℕ) (indices : List ℕ) (values : List ℤ) (v : ℤ)
    (hindex : List.range b.states.length = indices)
    (h : List.Forall₂ (fun i value => (moments b d i n).2.1 = value) indices values)
    (hs : values.sum = v) : total [b] d n = v := by
  unfold total numerator
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [hindex, sum_of_diagonal h, hs]

end Grain.HubbardChannels
