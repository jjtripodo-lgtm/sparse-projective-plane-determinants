import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace SparseComponent.TotalOnes
open Finset Real

/-- Exact rational gates for a logarithm, with a proved analytic remainder. -/
theorem log_interval_of_atanh (q : ℝ) (hq : 1 ≤ q) (n : ℕ) (lo hi : ℝ)
    (lower : lo ≤ 2 * ∑ i ∈ range n, ((q - 1) / (q + 1)) ^ (2*i+1) / (2*i+1))
    (upper : 2 * ((∑ i ∈ range n, ((q - 1) / (q + 1)) ^ (2*i+1) / (2*i+1)) +
      ((q - 1) / (q + 1)) ^ (2*n+1) / (1 - ((q - 1) / (q + 1))^2)) ≤ hi) :
    lo ≤ log q ∧ log q ≤ hi := by
  have hd : 0 < q + 1 := by linarith
  have h0 : 0 ≤ (q - 1) / (q + 1) := div_nonneg (by linarith) hd.le
  have h1 : (q - 1) / (q + 1) < 1 := (div_lt_one hd).mpr (by linarith)
  have he : (1 + (q - 1) / (q + 1)) / (1 - (q - 1) / (q + 1)) = q := by
    field_simp
    ring
  have hl := Real.sum_range_le_log_div h0 h1 n
  have hu := Real.log_div_le_sum_range_add h0 h1 n
  rw [he] at hl hu
  constructor <;> linarith

theorem log_nine_halves_bounds :
    (150407 : ℝ) / 100000 ≤ log (9/2) ∧ log (9/2) ≤ (150409 : ℝ) / 100000 := by
  apply log_interval_of_atanh (9/2) (by norm_num) 16
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_three_halves_bounds :
    (40546 : ℝ) / 100000 ≤ log (3/2) ∧ log (3/2) ≤ (40547 : ℝ) / 100000 := by
  apply log_interval_of_atanh (3/2) (by norm_num) 16
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_four_thirds_bounds :
    (28768 : ℝ) / 100000 ≤ log (4/3) ∧ log (4/3) ≤ (28769 : ℝ) / 100000 := by
  apply log_interval_of_atanh (4/3) (by norm_num) 16
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_five_thirds_bounds :
    (51082 : ℝ) / 100000 ≤ log (5/3) ∧ log (5/3) ≤ (51083 : ℝ) / 100000 := by
  apply log_interval_of_atanh (5/3) (by norm_num) 16
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_two_bounds :
    (69314 : ℝ) / 100000 ≤ log (2) ∧ log (2) ≤ (69315 : ℝ) / 100000 := by
  apply log_interval_of_atanh (2) (by norm_num) 16
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_seven_thirds_bounds :
    (84729 : ℝ) / 100000 ≤ log (7/3) ∧ log (7/3) ≤ (84730 : ℝ) / 100000 := by
  apply log_interval_of_atanh (7/3) (by norm_num) 16
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_eight_thirds_bounds :
    (98082 : ℝ) / 100000 ≤ log (8/3) ∧ log (8/3) ≤ (98083 : ℝ) / 100000 := by
  apply log_interval_of_atanh (8/3) (by norm_num) 16
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_three_bounds :
    (109861 : ℝ) / 100000 ≤ log (3) ∧ log (3) ≤ (109862 : ℝ) / 100000 := by
  apply log_interval_of_atanh (3) (by norm_num) 16
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_ten_thirds_bounds :
    (120397 : ℝ) / 100000 ≤ log (10/3) ∧ log (10/3) ≤ (120398 : ℝ) / 100000 := by
  apply log_interval_of_atanh (10/3) (by norm_num) 16
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

end SparseComponent.TotalOnes
