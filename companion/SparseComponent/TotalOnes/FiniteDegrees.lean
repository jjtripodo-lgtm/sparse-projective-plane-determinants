import SparseComponent.TotalOnes.Constants
import Mathlib.Tactic.IntervalCases

namespace SparseComponent.TotalOnes
open Real

/-- Rational interval gates certify a concave quadratic for every real argument. -/
theorem negative_quadratic_of_bounds (g L C gl lu cu u : ℝ)
    (hg : 0 < g) (hgl : gl ≤ g) (hL0 : 0 ≤ L) (hL : L ≤ lu)
    (hC : C ≤ cu) (hcu : cu ≤ 0) (gate : lu^2 + 324*gl*cu < 0) :
    -81*g*u^2 + L*u + C < 0 := by
  have hsq : L^2 ≤ lu^2 := by nlinarith
  have hgc : g*C ≤ gl*cu := calc
    _ ≤ g*cu := mul_le_mul_of_nonneg_left hC hg.le
    _ ≤ gl*cu := mul_le_mul_of_nonpos_right hgl hcu
  have hp : 0 < 324*g := by positivity
  apply (mul_lt_mul_iff_right₀ hp).mp
  have he : 324*g*(-81*g*u^2+L*u+C) = -(162*g*u-L)^2+L^2+324*g*C := by ring
  rw [mul_zero, he]
  nlinarith [sq_nonneg (162*g*u-L)]

theorem degree_2_strict (u : ℝ) : degreeGap 2 u < -(1 : ℝ)/100 := by
  have hL0 : 0 ≤ degreeLinear 2 := by
    unfold degreeLinear hermiteLinear balanceSlope
    norm_num
    linarith [curvature_bounds.1]
  have hL : degreeLinear 2 ≤ (13757 : ℝ)/5000 := by
    unfold degreeLinear hermiteLinear balanceSlope
    norm_num
    linarith [curvature_bounds.2]
  have hl : log (2/3 : ℝ) ≤ -(40546 : ℝ)/100000 := by
    have he : (2/3 : ℝ) = (3/2)⁻¹ := by norm_num
    rw [he, log_inv]
    linarith [log_three_halves_bounds.1]
  have hC : degreeConstant 2 + 1/100 ≤ (-57687 : ℝ)/100000 := by
    unfold degreeConstant edgeSlope
    norm_num at hl ⊢
    linarith [curvature_bounds.1]
  have h := negative_quadratic_of_bounds curvature (degreeLinear 2)
    (degreeConstant 2+1/100) (4073/100000) ((13757 : ℝ)/5000) ((-57687 : ℝ)/100000) u
    curvature_pos curvature_bounds.1 hL0 hL hC (by norm_num) (by norm_num)
  unfold degreeGap
  linarith

theorem degree_4_strict (u : ℝ) : degreeGap 4 u < -(1 : ℝ)/100 := by
  have hL0 : 0 ≤ degreeLinear 4 := by
    unfold degreeLinear hermiteLinear balanceSlope
    norm_num
    linarith [curvature_bounds.1]
  have hL : degreeLinear 4 ≤ (2247 : ℝ)/1250 := by
    unfold degreeLinear hermiteLinear balanceSlope
    norm_num
    linarith [curvature_bounds.2]
  have hl := log_four_thirds_bounds.2
  have hC : degreeConstant 4 + 1/100 ≤ (-25403 : ℝ)/100000 := by
    unfold degreeConstant edgeSlope
    norm_num at hl ⊢
    linarith [curvature_bounds.1]
  have h := negative_quadratic_of_bounds curvature (degreeLinear 4)
    (degreeConstant 4+1/100) (4073/100000) ((2247 : ℝ)/1250) ((-25403 : ℝ)/100000) u
    curvature_pos curvature_bounds.1 hL0 hL hC (by norm_num) (by norm_num)
  unfold degreeGap
  linarith

theorem degree_5_strict (u : ℝ) : degreeGap 5 u < -(1 : ℝ)/100 := by
  have hL0 : 0 ≤ degreeLinear 5 := by
    unfold degreeLinear hermiteLinear balanceSlope
    norm_num
    linarith [curvature_bounds.1]
  have hL : degreeLinear 5 ≤ (7191 : ℝ)/5000 := by
    unfold degreeLinear hermiteLinear balanceSlope
    norm_num
    linarith [curvature_bounds.2]
  have hl := log_five_thirds_bounds.2
  have hC : degreeConstant 5 + 1/100 ≤ (-4321 : ℝ)/20000 := by
    unfold degreeConstant edgeSlope
    norm_num at hl ⊢
    linarith [curvature_bounds.1]
  have h := negative_quadratic_of_bounds curvature (degreeLinear 5)
    (degreeConstant 5+1/100) (4073/100000) ((7191 : ℝ)/5000) ((-4321 : ℝ)/20000) u
    curvature_pos curvature_bounds.1 hL0 hL hC (by norm_num) (by norm_num)
  unfold degreeGap
  linarith

theorem degree_6_strict (u : ℝ) : degreeGap 6 u < -(1 : ℝ)/100 := by
  have hL0 : 0 ≤ degreeLinear 6 := by
    unfold degreeLinear hermiteLinear balanceSlope
    norm_num
    linarith [curvature_bounds.1]
  have hL : degreeLinear 6 ≤ (5479 : ℝ)/5000 := by
    unfold degreeLinear hermiteLinear balanceSlope
    norm_num
    linarith [curvature_bounds.2]
  have hl := log_two_bounds.2
  have hC : degreeConstant 6 + 1/100 ≤ (-21889 : ℝ)/100000 := by
    unfold degreeConstant edgeSlope
    norm_num at hl ⊢
    linarith [curvature_bounds.1]
  have h := negative_quadratic_of_bounds curvature (degreeLinear 6)
    (degreeConstant 6+1/100) (4073/100000) ((5479 : ℝ)/5000) ((-21889 : ℝ)/100000) u
    curvature_pos curvature_bounds.1 hL0 hL hC (by norm_num) (by norm_num)
  unfold degreeGap
  linarith

theorem degree_7_strict (u : ℝ) : degreeGap 7 u < -(1 : ℝ)/100 := by
  have hL0 : 0 ≤ degreeLinear 7 := by
    unfold degreeLinear hermiteLinear balanceSlope
    norm_num
    linarith [curvature_bounds.1]
  have hL : degreeLinear 7 ≤ (3807 : ℝ)/5000 := by
    unfold degreeLinear hermiteLinear balanceSlope
    norm_num
    linarith [curvature_bounds.2]
  have hl := log_seven_thirds_bounds.2
  have hC : degreeConstant 7 + 1/100 ≤ (-2499 : ℝ)/10000 := by
    unfold degreeConstant edgeSlope
    norm_num at hl ⊢
    linarith [curvature_bounds.1]
  have h := negative_quadratic_of_bounds curvature (degreeLinear 7)
    (degreeConstant 7+1/100) (4073/100000) ((3807 : ℝ)/5000) ((-2499 : ℝ)/10000) u
    curvature_pos curvature_bounds.1 hL0 hL hC (by norm_num) (by norm_num)
  unfold degreeGap
  linarith

theorem degree_8_strict (u : ℝ) : degreeGap 8 u < -(1 : ℝ)/100 := by
  have hL0 : 0 ≤ degreeLinear 8 := by
    unfold degreeLinear hermiteLinear balanceSlope
    norm_num
    linarith [curvature_bounds.1]
  have hL : degreeLinear 8 ≤ (4313 : ℝ)/10000 := by
    unfold degreeLinear hermiteLinear balanceSlope
    norm_num
    linarith [curvature_bounds.2]
  have hl := log_eight_thirds_bounds.2
  have hC : degreeConstant 8 + 1/100 ≤ (-30153 : ℝ)/100000 := by
    unfold degreeConstant edgeSlope
    norm_num at hl ⊢
    linarith [curvature_bounds.1]
  have h := negative_quadratic_of_bounds curvature (degreeLinear 8)
    (degreeConstant 8+1/100) (4073/100000) ((4313 : ℝ)/10000) ((-30153 : ℝ)/100000) u
    curvature_pos curvature_bounds.1 hL0 hL hC (by norm_num) (by norm_num)
  unfold degreeGap
  linarith

theorem degree_9_strict (u : ℝ) : degreeGap 9 u < -(1 : ℝ)/100 := by
  have hL0 : 0 ≤ degreeLinear 9 := by
    unfold degreeLinear hermiteLinear balanceSlope
    norm_num
    linarith [curvature_bounds.1]
  have hL : degreeLinear 9 ≤ (1037 : ℝ)/10000 := by
    unfold degreeLinear hermiteLinear balanceSlope
    norm_num
    linarith [curvature_bounds.2]
  have hl := log_three_bounds.2
  have hC : degreeConstant 9 + 1/100 ≤ (-3689 : ℝ)/10000 := by
    unfold degreeConstant edgeSlope
    norm_num at hl ⊢
    linarith [curvature_bounds.1]
  have h := negative_quadratic_of_bounds curvature (degreeLinear 9)
    (degreeConstant 9+1/100) (4073/100000) ((1037 : ℝ)/10000) ((-3689 : ℝ)/10000) u
    curvature_pos curvature_bounds.1 hL0 hL hC (by norm_num) (by norm_num)
  unfold degreeGap
  linarith

theorem finite_degree_strict (d : ℕ) (hd : 2 ≤ d) (h9 : d ≤ 9) (hne : d ≠ 3) (u : ℝ) :
    degreeGap d u < -(1 : ℝ)/100 := by
  interval_cases d <;> first
  | exact degree_2_strict u
  | exact degree_4_strict u
  | exact degree_5_strict u
  | exact degree_6_strict u
  | exact degree_7_strict u
  | exact degree_8_strict u
  | exact degree_9_strict u
  | omega

end SparseComponent.TotalOnes
