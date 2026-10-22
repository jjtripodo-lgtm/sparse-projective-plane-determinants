import SparseComponent.TotalOnes.DegreeMajorant
namespace SparseComponent.TotalOnes.Controls
open Real
example (u : ℝ) : degreeGap 3 u = -81*curvature*(u-1/3)^2 := degree_three_gap u
example (u : ℝ) : degreeGap 2 u < -(1 : ℝ)/100 := degree_2_strict u
example : degreeGap (200001/2) 0 < -(1 : ℝ)/100 :=
  tail_degree_strict _ _ (by norm_num) (by norm_num)
example : 0 < fanoRate - 2*edgeSlope := by linarith [peeling_margin]
/-- Degree one does fail the pointwise majorant; the full theorem must peel it. -/
theorem degree_one_countercontrol : 0 < degreeGap 1 (1/2) := by
  have hl : log (1/3 : ℝ) = -log 3 := by
    rw [log_div (by norm_num) (by norm_num), log_one]
    ring
  unfold degreeGap degreeLinear degreeConstant hermiteLinear balanceSlope edgeSlope
  norm_num
  linarith [curvature_bounds.1, log_three_bounds.2]
end SparseComponent.TotalOnes.Controls
