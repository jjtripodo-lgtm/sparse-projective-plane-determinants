import SparseComponent.TotalFamily.LogCertificates

namespace SparseComponent.TotalFamily.Density4
open Finset Matrix Real TotalOnes Certificates

theorem gamma_bounds : (1573583:ℝ)/100000000 ≤ gamma 4 ∧ gamma 4 ≤ (314717:ℝ)/20000000 := by
  have h := log_16_3_bounds
  unfold gamma logGamma
  rw [← log_div (by norm_num : (4:ℝ)^2 ≠ 0) (by norm_num : (4:ℝ)-1 ≠ 0)]
  norm_num at h ⊢
  constructor <;> linarith

theorem degree_2_strict (u : ℝ) (hu : 0 ≤ u) : negativeGap 4 2 u < 0 := by
  have hL0 : 0 ≤ degreeLinear 4 2 := by
    unfold degreeLinear balance
    norm_num
    linarith [gamma_bounds.1]
  have hL : degreeLinear 4 2 ≤ (47380379:ℝ)/15000000 := by
    unfold degreeLinear balance
    norm_num
    linarith [gamma_bounds.2]
  have hl : log ((2:ℝ)/4) ≤ (-693147:ℝ)/1000000 := by
    rw [show (2:ℝ)/4 = ((2:ℝ)/1)⁻¹ by norm_num, log_inv]
    linarith [log_2_1_bounds.1]
  have hC : degreeConstant 4 2 ≤ (-200430841:ℝ)/300000000 := by
    unfold degreeConstant slope
    norm_num at hl ⊢
    linarith [gamma_bounds.1]
  have h := negative_quadratic_gate (gamma 4*4^4) (degreeLinear 4 2)
    (degreeConstant 4 2) ((1573583:ℝ)/390625) ((47380379:ℝ)/15000000) ((-200430841:ℝ)/300000000) u
    (by have := gamma_positive (4:ℝ) (by norm_num); positivity)
    (by nlinarith [gamma_bounds.1]) hL0 hL hC (by norm_num) (by norm_num)
  simpa only [negativeGap, neg_mul] using h

theorem degree_3_strict (u : ℝ) (hu : 0 ≤ u) : negativeGap 4 3 u < 0 := by
  have hL0 : 0 ≤ degreeLinear 4 3 := by
    unfold degreeLinear balance
    norm_num
    linarith [gamma_bounds.1]
  have hL : degreeLinear 4 3 ≤ (224596991:ℝ)/90000000 := by
    unfold degreeLinear balance
    norm_num
    linarith [gamma_bounds.2]
  have hl : log ((3:ℝ)/4) ≤ (-143841:ℝ)/500000 := by
    rw [show (3:ℝ)/4 = ((4:ℝ)/3)⁻¹ by norm_num, log_inv]
    linarith [log_4_3_bounds.1]
  have hC : degreeConstant 4 3 ≤ (-9625117:ℝ)/24000000 := by
    unfold degreeConstant slope
    norm_num at hl ⊢
    linarith [gamma_bounds.1]
  have h := negative_quadratic_gate (gamma 4*4^4) (degreeLinear 4 3)
    (degreeConstant 4 3) ((1573583:ℝ)/390625) ((224596991:ℝ)/90000000) ((-9625117:ℝ)/24000000) u
    (by have := gamma_positive (4:ℝ) (by norm_num); positivity)
    (by nlinarith [gamma_bounds.1]) hL0 hL hC (by norm_num) (by norm_num)
  simpa only [negativeGap, neg_mul] using h

theorem degree_5_strict (u : ℝ) (hu : 0 ≤ u) : negativeGap 4 5 u < 0 := by
  have hL0 : 0 ≤ degreeLinear 4 5 := by
    unfold degreeLinear balance
    norm_num
    linarith [gamma_bounds.1]
  have hL : degreeLinear 4 5 ≤ (1189086139:ℝ)/750000000 := by
    unfold degreeLinear balance
    norm_num
    linarith [gamma_bounds.2]
  have hl : log ((5:ℝ)/4) ≤ (27893:ℝ)/125000 := by
    convert log_5_4_bounds.2 using 1 <;> norm_num
  have hC : degreeConstant 4 5 ≤ (-100222811:ℝ)/600000000 := by
    unfold degreeConstant slope
    norm_num at hl ⊢
    linarith [gamma_bounds.1]
  have h := negative_quadratic_gate (gamma 4*4^4) (degreeLinear 4 5)
    (degreeConstant 4 5) ((1573583:ℝ)/390625) ((1189086139:ℝ)/750000000) ((-100222811:ℝ)/600000000) u
    (by have := gamma_positive (4:ℝ) (by norm_num); positivity)
    (by nlinarith [gamma_bounds.1]) hL0 hL hC (by norm_num) (by norm_num)
  simpa only [negativeGap, neg_mul] using h

theorem degree_6_strict (u : ℝ) (hu : 0 ≤ u) : negativeGap 4 6 u < 0 := by
  have hL0 : 0 ≤ degreeLinear 4 6 := by
    unfold degreeLinear balance
    norm_num
    linarith [gamma_bounds.1]
  have hL : degreeLinear 4 6 ≤ (52983403:ℝ)/45000000 := by
    unfold degreeLinear balance
    norm_num
    linarith [gamma_bounds.2]
  have hl : log ((6:ℝ)/4) ≤ (202733:ℝ)/500000 := by
    convert log_3_2_bounds.2 using 1 <;> norm_num
  have hC : degreeConstant 4 6 ≤ (-36937427:ℝ)/300000000 := by
    unfold degreeConstant slope
    norm_num at hl ⊢
    linarith [gamma_bounds.1]
  have h := negative_quadratic_gate (gamma 4*4^4) (degreeLinear 4 6)
    (degreeConstant 4 6) ((1573583:ℝ)/390625) ((52983403:ℝ)/45000000) ((-36937427:ℝ)/300000000) u
    (by have := gamma_positive (4:ℝ) (by norm_num); positivity)
    (by nlinarith [gamma_bounds.1]) hL0 hL hC (by norm_num) (by norm_num)
  simpa only [negativeGap, neg_mul] using h

theorem degree_7_strict (u : ℝ) (hu : 0 ≤ u) : negativeGap 4 7 u < 0 := by
  have hL0 : 0 ≤ degreeLinear 4 7 := by
    unfold degreeLinear balance
    norm_num
    linarith [gamma_bounds.1]
  have hL : degreeLinear 4 7 ≤ (381780459:ℝ)/490000000 := by
    unfold degreeLinear balance
    norm_num
    linarith [gamma_bounds.2]
  have hl : log ((7:ℝ)/4) ≤ (8744:ℝ)/15625 := by
    convert log_7_4_bounds.2 using 1 <;> norm_num
  have hC : degreeConstant 4 7 ≤ (-21476699:ℝ)/200000000 := by
    unfold degreeConstant slope
    norm_num at hl ⊢
    linarith [gamma_bounds.1]
  have h := negative_quadratic_gate (gamma 4*4^4) (degreeLinear 4 7)
    (degreeConstant 4 7) ((1573583:ℝ)/390625) ((381780459:ℝ)/490000000) ((-21476699:ℝ)/200000000) u
    (by have := gamma_positive (4:ℝ) (by norm_num); positivity)
    (by nlinarith [gamma_bounds.1]) hL0 hL hC (by norm_num) (by norm_num)
  simpa only [negativeGap, neg_mul] using h

theorem degree_8_strict (u : ℝ) (hu : 0 ≤ u) : negativeGap 4 8 u < 0 := by
  have hL0 : 0 ≤ degreeLinear 4 8 := by
    unfold degreeLinear balance
    norm_num
    linarith [gamma_bounds.1]
  have hL : degreeLinear 4 8 ≤ (11582647:ℝ)/30000000 := by
    unfold degreeLinear balance
    norm_num
    linarith [gamma_bounds.2]
  have hl : log ((8:ℝ)/4) ≤ (173287:ℝ)/250000 := by
    convert log_2_1_bounds.2 using 1 <;> norm_num
  have hC : degreeConstant 4 8 ≤ (-3367807:ℝ)/30000000 := by
    unfold degreeConstant slope
    norm_num at hl ⊢
    linarith [gamma_bounds.1]
  have h := negative_quadratic_gate (gamma 4*4^4) (degreeLinear 4 8)
    (degreeConstant 4 8) ((1573583:ℝ)/390625) ((11582647:ℝ)/30000000) ((-3367807:ℝ)/30000000) u
    (by have := gamma_positive (4:ℝ) (by norm_num); positivity)
    (by nlinarith [gamma_bounds.1]) hL0 hL hC (by norm_num) (by norm_num)
  simpa only [negativeGap, neg_mul] using h

theorem tail_strict (d u : ℝ) (hd : 9 ≤ d) (hu : 0 ≤ u) : negativeGap 4 d u < 0 := by
  apply tail_gap_negative 4 9 d u (by norm_num) (by norm_num) hd hu
  · unfold balance; norm_num; linarith [gamma_bounds.2]
  · unfold slope; norm_num; linarith [gamma_bounds.1]
  · unfold degreeLinear balance; norm_num; linarith [gamma_bounds.2]
  · unfold degreeConstant slope
    have hl := log_9_4_bounds.2
    norm_num at hl ⊢
    linarith [gamma_bounds.1]

theorem vertex_certificate (d : ℤ) (hd : 2 ≤ d) (u : ℝ) (hu : 0 ≤ u) : 0 ≤ deficit 4 d u := by
  by_cases he : d = 4
  · subst d
    rw [Int.cast_ofNat, deficit_plane_degree 4 u (by norm_num)]
    have := gamma_positive (4:ℝ) (by norm_num)
    positivity
  have hn : negativeGap 4 d u < 0 := by
    by_cases ht : 9 ≤ d
    · exact tail_strict d u (by exact_mod_cast ht) hu
    · interval_cases d <;> norm_num at * <;> first
      | exact degree_2_strict u hu
      | exact degree_3_strict u hu
      | exact degree_5_strict u hu
      | exact degree_6_strict u hu
      | exact degree_7_strict u hu
      | exact degree_8_strict u hu
      | contradiction
  rw [negativeGap_eq_neg_deficit 4 d u (by norm_num)] at hn
  linarith

theorem peeling_margin : slope 4*(4-1) < rate 4 := by
  have hr := log_4_1_bounds.1
  have ht := log_3_1_bounds.1
  unfold slope rate planeOrder
  norm_num at hr ht ⊢
  linarith [gamma_bounds.2]

/-- Complete unrestricted density-4 exponential determinant theorem. -/
theorem determinant_total_ones (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) (hA : Binary A) :
    |(A.det:ℝ)| ≤ exp (exponent 4 n (edgeCount A)) :=
  determinant_from_vertex_certificate 4 (by norm_num) vertex_certificate peeling_margin n A hA

theorem determinant_total_4_ones (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : Binary A) (he : edgeCount A ≤ 4*(n:ℤ)) :
    |(A.det:ℝ)| ≤ exp ((n:ℝ)*rate 4) := by
  apply (determinant_total_ones n A hA).trans
  apply exp_le_exp.mpr
  unfold exponent
  have he' : (edgeCount A:ℝ)-4*(n:ℝ) ≤ 0 := by exact_mod_cast sub_nonpos.mpr he
  have hm := mul_nonpos_of_nonneg_of_nonpos (slope_pos 4 (by norm_num)).le he'
  linarith

end SparseComponent.TotalFamily.Density4
