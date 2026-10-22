import SparseComponent.TotalOnes.FiniteDegrees

namespace SparseComponent.TotalOnes
open Real

theorem degreeLinear_ten_negative : degreeLinear 10 < 0 := by
  unfold degreeLinear hermiteLinear balanceSlope
  norm_num
  linarith [curvature_bounds.2]

theorem degreeLinear_tail (d : ℝ) (hd : 10 ≤ d) : degreeLinear d ≤ degreeLinear 10 := by
  have hsq : (100 : ℝ) ≤ d^2 := by nlinarith
  have hfrac : 81*curvature/(2*d^2) ≤ 81*curvature/(2*10^2) := by
    apply div_le_div_of_nonneg_left (mul_nonneg (by norm_num) curvature_pos.le) (by norm_num)
    linarith
  have hb := mul_le_mul_of_nonneg_left hd balanceSlope_pos.le
  unfold degreeLinear
  linarith

theorem degreeConstant_ten_negative : degreeConstant 10 < -(1 : ℝ)/100 := by
  unfold degreeConstant edgeSlope
  norm_num
  linarith [log_ten_thirds_bounds.2, curvature_bounds.1]

theorem degreeConstant_tail (d : ℝ) (hd : 10 ≤ d) : degreeConstant d ≤ degreeConstant 10 := by
  have hp : 0 < d/10 := by linarith
  have hl := Real.log_le_sub_one_of_pos hp
  have he : log (d/3) = log (d/10) + log (10/3 : ℝ) := by
    rw [← log_mul hp.ne' (by norm_num)]
    congr 1
    ring
  have hs := mul_nonneg (show 0 ≤ edgeSlope-1/10 by linarith [edgeSlope_gt_tenth])
    (show 0 ≤ d-10 by linarith)
  unfold degreeConstant
  rw [he]
  linarith

/-- The unbounded tail is controlled analytically, without a finite degree cutoff. -/
theorem tail_degree_strict (d u : ℝ) (hd : 10 ≤ d) (hu : 0 ≤ u) :
    degreeGap d u < -(1 : ℝ)/100 := by
  have hL : degreeLinear d ≤ 0 := (degreeLinear_tail d hd).trans degreeLinear_ten_negative.le
  have hC := (degreeConstant_tail d hd).trans_lt degreeConstant_ten_negative
  have hLu := mul_nonpos_of_nonpos_of_nonneg hL hu
  have hsq := mul_nonneg curvature_pos.le (sq_nonneg u)
  unfold degreeGap
  nlinarith

theorem nonthree_degree_strict (d : ℕ) (hd : 2 ≤ d) (hne : d ≠ 3) (u : ℝ) (hu : 0 ≤ u) :
    degreeGap d u < -(1 : ℝ)/100 := by
  by_cases h9 : d ≤ 9
  · exact finite_degree_strict d hd h9 hne u
  · apply tail_degree_strict d u _ hu
    exact_mod_cast (show 10 ≤ d by omega)

/-- The complete integer-degree majorant used for every original row and column. -/
theorem degree_majorant (d : ℕ) (hd : 2 ≤ d) (u : ℝ) (hu : 0 ≤ u) :
    degreeTerm d u ≤ baseDegreeValue + edgeSlope*(d-3) + balanceSlope*(d*u-1) := by
  have he := degree_gap_identity d u
  by_cases h3 : d = 3
  · subst d
    rw [Nat.cast_ofNat, degree_three_gap] at he
    norm_num at he ⊢
    have hs := mul_nonneg curvature_pos.le (sq_nonneg (u-1/3))
    nlinarith
  · have h := nonthree_degree_strict d hd h3 u hu
    linarith

theorem degree_majorant_eq_iff (d : ℕ) (hd : 2 ≤ d) (u : ℝ) (hu : 0 ≤ u) :
    degreeTerm d u = baseDegreeValue + edgeSlope*(d-3) + balanceSlope*(d*u-1) ↔
      d = 3 ∧ u = 1/3 := by
  have he := degree_gap_identity d u
  constructor
  · intro h
    have hz : degreeGap d u = 0 := by linarith
    have h3 : d = 3 := by
      by_contra hn
      have hh := nonthree_degree_strict d hd hn u hu
      linarith
    refine ⟨h3, ?_⟩
    subst d
    rw [Nat.cast_ofNat, degree_three_gap] at hz
    have hsq : (u-1/3)^2 = 0 := by nlinarith [sq_nonneg (u-1/3), curvature_pos]
    nlinarith
  · rintro ⟨rfl, rfl⟩
    rw [Nat.cast_ofNat, degree_three_gap] at he
    norm_num at he
    linarith

/-- Integer form for the literal row and column sums of an integer binary matrix. -/
theorem degree_majorant_int (d : ℤ) (hd : 2 ≤ d) (u : ℝ) (hu : 0 ≤ u) :
    degreeTerm d u ≤ baseDegreeValue + edgeSlope*(d-3) + balanceSlope*(d*u-1) := by
  have hn : 2 ≤ d.toNat := by omega
  have hc : (d.toNat : ℝ) = d := by
    exact_mod_cast (Int.toNat_of_nonneg (show 0 ≤ d by omega))
  simpa only [hc] using degree_majorant d.toNat hn u hu

theorem degree_majorant_int_eq_iff (d : ℤ) (hd : 2 ≤ d) (u : ℝ) (hu : 0 ≤ u) :
    degreeTerm d u = baseDegreeValue + edgeSlope*(d-3) + balanceSlope*(d*u-1) ↔
      d = 3 ∧ u = 1/3 := by
  have hn : 2 ≤ d.toNat := by omega
  have hc : (d.toNat : ℝ) = d := by
    exact_mod_cast (Int.toNat_of_nonneg (show 0 ≤ d by omega))
  have h := degree_majorant_eq_iff d.toNat hn u hu
  rw [hc] at h
  have hi : d.toNat = 3 ↔ d = 3 := by omega
  rwa [hi] at h

end SparseComponent.TotalOnes
