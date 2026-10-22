import SparseComponent.Parameters

namespace SparseComponent
open Real

theorem gamma_charge_constant (r : ℝ) (hr : 2 ≤ r) :
    planeOrder r * stabilityCoefficient r ≤ 2 * gamma r := by
  have hr0 : 0 < r := by linarith
  have ht : 0 < r - 1 := by linarith
  have hv := planeOrder_positive r
  have hvle : planeOrder r ≤ r ^ 2 := by unfold planeOrder; linarith
  have hprod : planeOrder r * ((r - 1) * r ^ 2) ≤ r ^ 5 := by
    calc
      _ ≤ r ^ 2 * (r * r ^ 2) := mul_le_mul hvle
        (mul_le_mul_of_nonneg_right (by linarith : r - 1 ≤ r) (sq_nonneg _))
        (by positivity) (sq_nonneg _)
      _ = _ := by ring
  have hp5 : r ^ 5 ≤ 6 * r ^ 6 := by
    have h := mul_le_mul_of_nonneg_right (by linarith : (1 : ℝ) ≤ 6 * r)
      (show 0 ≤ r ^ 5 by positivity)
    nlinarith
  calc
    planeOrder r * stabilityCoefficient r = planeOrder r / (6 * r ^ 6) := by
      unfold stabilityCoefficient; ring
    _ ≤ 1 / ((r - 1) * r ^ 2) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith [hprod.trans hp5]
    _ = 2 * (1 / (2 * (r - 1) * r ^ 2)) := by field_simp
    _ ≤ 2 * gamma r := mul_le_mul_of_nonneg_left (gamma_lower r hr) (by norm_num)

theorem delta_large_lower (r : ℝ) (hr : 4 ≤ r) : 1 / r ^ 2 ≤ delta r := by
  have hr0 : 0 < r := by linarith
  have ht : 0 < r - 1 := by linarith
  have hv := planeOrder_positive r
  have hu : 1 ≤ r ^ 2 / (r - 1) := (le_div_iff₀ ht).mpr (by nlinarith)
  have hlog : 0 ≤ log (r ^ 2 / (r - 1)) := log_nonneg hu
  have hterm : 0 ≤ (2 * r + 1) * log (r ^ 2 / (r - 1)) / planeOrder r ^ 2 := by positivity
  rw [delta_decomposition r (by linarith)]
  have hprod : (r - 1) * planeOrder r ≤ r ^ 3 := by
    unfold planeOrder
    nlinarith [sq_nonneg (r - 1)]
  have hp : r ^ 3 ≤ r ^ 3 * (r - 3) := by
    exact le_mul_of_one_le_right (by positivity) (by linarith)
  have hbase : 1 / r ^ 2 ≤ r * (r - 3) / ((r - 1) * planeOrder r) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [hprod.trans hp]
  linarith

theorem delta_two_lower : (2 : ℝ) / 27 ≤ delta 2 := by
  have h := delta_decomposition 2 (by norm_num)
  norm_num [planeOrder] at h
  linarith [log_four_lower]

theorem delta_three_lower : (4 : ℝ) / 21 ≤ delta 3 := by
  have h := delta_decomposition 3 (by norm_num)
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 4) (by norm_num : (4 : ℝ) ≤ 3 ^ 2 / (3 - 1))
  norm_num [planeOrder] at h hl
  linarith [log_four_lower]

/-- The stated uniform constant for every integer cap, including 2 and 3. -/
theorem delta_charge_constant (r : ℕ) (hr : 2 ≤ r) :
    stabilityCoefficient r ≤ delta r / 2 := by
  by_cases h2 : r = 2
  · subst r
    norm_num [stabilityCoefficient]
    linarith [delta_two_lower]
  by_cases h3 : r = 3
  · subst r
    norm_num [stabilityCoefficient]
    linarith [delta_three_lower]
  have hr4 : (4 : ℝ) ≤ r := by exact_mod_cast (show 4 ≤ r by omega)
  have hr0 : (0 : ℝ) < r := by linarith
  have hd := delta_large_lower r hr4
  have hp : (r : ℝ) ^ 2 ≤ 3 * (r : ℝ) ^ 6 := by
    have h4 : (1 : ℝ) ≤ (r : ℝ) ^ 4 := one_le_pow₀ (by linarith)
    have h := mul_le_mul_of_nonneg_right h4 (sq_nonneg (r : ℝ))
    nlinarith [sq_nonneg ((r : ℝ) ^ 3)]
  have hc : stabilityCoefficient r ≤ (1 / (r : ℝ) ^ 2) / 2 := by
    unfold stabilityCoefficient
    rw [div_div]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  exact hc.trans (div_le_div_of_nonneg_right hd (by norm_num))

theorem stabilityCoefficient_positive (r : ℝ) (hr : 0 < r) : 0 < stabilityCoefficient r := by
  unfold stabilityCoefficient
  positivity

end SparseComponent
