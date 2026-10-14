import Mathlib

/-!
The integer coefficients below are certificates extracted from the recorded
L=12, 64-replica, q=4/5 and q=3/7 auxiliary-prepared random-start bitstrings.
Lean verifies the algebraic consequences of those coefficients. It does not
verify extraction of the coefficients from the external JSONL files.
-/
namespace LatticeGas.Numerics

def scale : ℕ := 10^40
def sqrt3Floor : ℕ := 17320508075688772935274463415058723669428

theorem sqrt3_integer_bracket :
    sqrt3Floor ^ 2 ≤ 3 * scale ^ 2 ∧
      3 * scale ^ 2 < (sqrt3Floor + 1) ^ 2 := by
  norm_num [sqrt3Floor, scale]

theorem sqrt3_real_bracket :
    (sqrt3Floor : ℝ) / scale ≤ Real.sqrt 3 ∧
      Real.sqrt 3 < ((sqrt3Floor + 1 : ℕ) : ℝ) / scale := by
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hp : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hl : ((sqrt3Floor : ℝ) / scale) ^ 2 ≤ 3 := by
    norm_num [sqrt3Floor, scale]
  have hu : 3 < ((((sqrt3Floor + 1 : ℕ) : ℝ) / scale) ^ 2) := by
    norm_num [sqrt3Floor, scale]
  have hpl : 0 ≤ (sqrt3Floor : ℝ) / scale := by positivity
  have hpu : 0 ≤ ((sqrt3Floor + 1 : ℕ) : ℝ) / scale := by positivity
  constructor <;> nlinarith

noncomputable def farPower : ℝ := (418188 + 44744 * Real.sqrt 3) / 663552
noncomputable def nearPower : ℝ := (2440980 + 1203140 * Real.sqrt 3) / 663552

theorem near_power_gt_nine_far : 9 * farPower < nearPower := by
  have hs : (17 / 10 : ℝ) < Real.sqrt 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
      Real.sqrt_nonneg 3]
  dsimp [farPower, nearPower]
  nlinarith

theorem near_power_lt_ten_far : nearPower < 10 * farPower := by
  have hs : Real.sqrt 3 < (2 : ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
      Real.sqrt_nonneg 3]
  dsimp [farPower, nearPower]
  nlinarith

end LatticeGas.Numerics
