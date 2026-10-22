import SparseComponent.TotalOnes.LogCertificates

namespace SparseComponent.TotalOnes
open Real

noncomputable def curvature : ℝ := ((7 : ℝ)/2 - log (9/2)) / 49
noncomputable def edgeSlope : ℝ := 1/12 + 5*curvature/2
noncomputable def balanceSlope : ℝ := 3/4 - 21*curvature/2
noncomputable def fanoRate : ℝ := log 24 / 7
noncomputable def hermiteLinear : ℝ := 1/2 + 4*curvature
noncomputable def hermiteConstant : ℝ := log 2 - 1 - 4*curvature
noncomputable def baseDegreeValue : ℝ := 3/4 - 3*curvature/2

noncomputable def degreeTerm (d u : ℝ) : ℝ :=
  (9*hermiteLinear/2 + 81*curvature/(2*d^2))*u - 81*curvature*u^2 + log (d/3)
noncomputable def degreeLinear (d : ℝ) : ℝ :=
  9*hermiteLinear/2 + 81*curvature/(2*d^2) - balanceSlope*d
noncomputable def degreeConstant (d : ℝ) : ℝ :=
  log (d/3) - edgeSlope*(d-3) - 9*curvature
noncomputable def degreeGap (d u : ℝ) : ℝ :=
  -81*curvature*u^2 + degreeLinear d*u + degreeConstant d

theorem curvature_bounds : (4073 : ℝ)/100000 ≤ curvature ∧ curvature ≤ (4074 : ℝ)/100000 := by
  unfold curvature
  constructor <;> linarith [log_nine_halves_bounds.1, log_nine_halves_bounds.2]

theorem curvature_pos : 0 < curvature := lt_of_lt_of_le (by norm_num) curvature_bounds.1

theorem balanceSlope_pos : 0 < balanceSlope := by
  unfold balanceSlope
  linarith [curvature_bounds.2]

theorem edgeSlope_gt_tenth : (1 : ℝ)/10 < edgeSlope := by
  unfold edgeSlope
  linarith [curvature_bounds.1]

theorem edgeSlope_pos : 0 < edgeSlope := by linarith [edgeSlope_gt_tenth]

theorem log_twentyfour : log (24 : ℝ) = log 3 + 3*log 2 := by
  have h : (24 : ℝ) = 3 * 2^3 := by norm_num
  rw [h, log_mul (by norm_num) (by norm_num), log_pow]
  norm_num

theorem peeling_margin : (1 : ℝ)/20 < fanoRate - 2*edgeSlope := by
  unfold fanoRate edgeSlope
  rw [log_twentyfour]
  linarith [log_three_bounds.1, log_two_bounds.1, curvature_bounds.2]

theorem degree_gap_identity (d u : ℝ) :
    degreeTerm d u - (baseDegreeValue + edgeSlope*(d-3) + balanceSlope*(d*u-1)) =
      degreeGap d u := by
  unfold degreeTerm baseDegreeValue degreeGap degreeLinear degreeConstant balanceSlope
  ring

theorem degree_three_gap (u : ℝ) : degreeGap 3 u = -81*curvature*(u-1/3)^2 := by
  unfold degreeGap degreeLinear degreeConstant hermiteLinear balanceSlope
  norm_num
  ring

theorem base_identity : hermiteConstant + 2*baseDegreeValue = 2*fanoRate := by
  have h : log (9/2 : ℝ) = 2*log 3 - log 2 := by
    rw [log_div (by norm_num) (by norm_num)]
    have h9 : log (9 : ℝ) = 2*log 3 := by
      convert log_pow (3 : ℝ) 2 using 1 <;> norm_num
    rw [h9]
  unfold hermiteConstant baseDegreeValue fanoRate curvature
  rw [h, log_twentyfour]
  ring

end SparseComponent.TotalOnes
