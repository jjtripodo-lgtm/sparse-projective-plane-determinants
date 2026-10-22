import SparseComponent.LogMajorant

namespace SparseComponent
open Real Set

theorem monotoneOn_positive_of_derivative {f f' : ℝ → ℝ}
    (hf : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (hp : ∀ x, 0 < x → 0 ≤ f' x) : MonotoneOn f (Ioi 0) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioi 0)
  · exact fun x hx => (hf x hx).continuousAt.continuousWithinAt
  · intro x hx
    apply (hf x _).hasDerivWithinAt
    simpa using hx
  · intro x hx
    apply hp x
    simpa using hx

/-- A rational upper bound for log with a uniform quadratic improvement. -/
theorem log_le_half_sub_inv (x : ℝ) (hx : 1 ≤ x) : log x ≤ (x - x⁻¹) / 2 := by
  have hd : ∀ z : ℝ, 0 < z → HasDerivAt (fun y : ℝ => (y - y⁻¹) / 2 - log y)
      ((z - 1) ^ 2 / (2 * z ^ 2)) z := by
    intro z hz
    convert! (((hasDerivAt_id z).sub (hasDerivAt_inv hz.ne')).div_const 2).sub
      (Real.hasDerivAt_log hz.ne') using 1
    try dsimp
    field_simp
    ring
  have hm := monotoneOn_positive_of_derivative hd
    (fun z hz => div_nonneg (sq_nonneg _) (by positivity))
  have h := hm (by norm_num : (1 : ℝ) ∈ Ioi 0) (by change 0 < x; linarith) hx
  norm_num at h
  linarith

/-- A rational lower bound for log; at two it gives log 2 >= 2/3. -/
theorem two_sub_div_add_le_log (x : ℝ) (hx : 1 ≤ x) : 2 * (x - 1) / (x + 1) ≤ log x := by
  have hd : ∀ z : ℝ, 0 < z → HasDerivAt (fun y : ℝ => log y - 2 * (y - 1) / (y + 1))
      ((z - 1) ^ 2 / (z * (z + 1) ^ 2)) z := by
    intro z hz
    have hn : z + 1 ≠ 0 := by linarith
    convert! (Real.hasDerivAt_log hz.ne').sub
      ((((hasDerivAt_id z).sub_const 1).const_mul 2).div ((hasDerivAt_id z).add_const 1) hn) using 1
    try dsimp
    field_simp
    ring
  have hm := monotoneOn_positive_of_derivative hd
    (fun z hz => div_nonneg (sq_nonneg _) (by positivity))
  have h := hm (by norm_num : (1 : ℝ) ∈ Ioi 0) (by change 0 < x; linarith) hx
  norm_num at h
  linarith

theorem log_four_lower : (4 : ℝ) / 3 ≤ log 4 := by
  have h := two_sub_div_add_le_log 2 (by norm_num)
  have hlog : log (4 : ℝ) = 2 * log 2 := by
    convert log_pow (2 : ℝ) 2 using 1 <;> norm_num
  norm_num at h
  linarith

end SparseComponent
