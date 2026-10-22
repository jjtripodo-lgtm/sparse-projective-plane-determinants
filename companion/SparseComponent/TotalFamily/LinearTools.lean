import SparseComponent.TotalFamily.Anchors

namespace SparseComponent.TotalFamily
open Real

theorem baseValue_explicit (r : ℝ) (hr : 2 ≤ r) :
    baseValue r = r/(2*(r-1))-gamma r*r/2 := by
  have hr0 : r ≠ 0 := by linarith
  have ht : r-1 ≠ 0 := by linarith
  unfold baseValue vertex logB gamma
  rw [div_self hr0, log_one]
  field_simp
  ring

noncomputable def linearPoly (r x y : ℝ) : ℝ :=
  2/r-1/(r-1)+(x+y)/(r-1)-r^2/(r-1)*x*y + gamma r*(
    2*r-1-r^2*(x+y)-2*r^2*(r-1)*x*y +
    r^4*(-x*(linearAnchor r x)^2-y*(linearAnchor r y)^2 +
      2*x*y*(linearAnchor r x+linearAnchor r y)-(x^3*y+x*y^3)/2))

theorem linear_edge_polynomial (r x y : ℝ) (hr : 2 ≤ r) :
    edgePolynomial r (linearAnchor r) x y + edgePolynomial r (linearAnchor r) y x =
      linearPoly r x y + x*log (r*x)+y*log (r*y) := by
  simp only [edgePolynomial, baseValue_explicit r hr, slope, balance, logB, linearPoly]
  have hr0 : r ≠ 0 := by linarith
  have ht : r-1 ≠ 0 := by linarith
  simp only [gamma]
  field_simp [hr0, ht]
  ring

/-- On a small reciprocal-degree tail, x log(r x) is bounded below by its upper endpoint.
The proof uses only log z <= z-1, not an imported monotonicity oracle. -/
theorem xlog_tail_lower (r U x : ℝ) (hr : 0 < r) (hU : 0 < U)
    (hx : 0 < x) (hxu : x ≤ U) (hlog : log (r*U) ≤ -1) :
    U*log (r*U) ≤ x*log (r*x) := by
  have hrat : 0 < U/x := div_pos hU hx
  have hl := log_le_sub_one_of_pos hrat
  have he : log (r*x) = log (r*U)-log (U/x) := by
    rw [log_mul hr.ne' hx.ne', log_mul hr.ne' hU.ne', log_div hU.ne' hx.ne']
    ring
  have hb := mul_le_mul_of_nonneg_left hl hx.le
  have hh : x*(U/x-1) = U-x := by field_simp
  rw [hh] at hb
  have hs := mul_nonneg (sub_nonneg.mpr hxu) (show 0 ≤ -1-log (r*U) by linarith)
  rw [he]
  nlinarith

theorem nonnegative_power_bounds (x U : ℝ) (hx : 0 ≤ x) (hxu : x ≤ U) (k : ℕ) :
    0 ≤ x^k ∧ x^k ≤ U^k := by
  exact ⟨pow_nonneg hx k, pow_le_pow_left₀ hx hxu k⟩

/-- A coefficient lower bound times a nonnegative bounded monomial. -/
theorem monomial_lower (a lo z U : ℝ) (ha : lo ≤ a) (hz : 0 ≤ z) (hzU : z ≤ U) :
    min 0 (lo*U) ≤ a*z := by
  apply le_trans _ (mul_le_mul_of_nonneg_right ha hz)
  by_cases hl : 0 ≤ lo
  · exact (min_le_left _ _).trans (mul_nonneg hl hz)
  · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left hzU (le_of_not_ge hl))
end SparseComponent.TotalFamily
