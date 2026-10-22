import SparseComponent.TotalFamily.LogCertificates

namespace SparseComponent.TotalFamily.Density6
open Finset Matrix Real TotalOnes Certificates

theorem gamma_bounds : (439741:ℝ)/100000000 ≤ gamma 6 ∧ gamma 6 ≤ (219871:ℝ)/50000000 := by
  have h := log_36_5_bounds
  unfold gamma logGamma
  rw [← log_div (by norm_num : (6:ℝ)^2 ≠ 0) (by norm_num : (6:ℝ)-1 ≠ 0)]
  norm_num at h ⊢
  constructor <;> linarith

theorem degree_2_strict (u : ℝ) (hu : 0 ≤ u) : negativeGap 6 2 u < 0 := by
  have hL0 : 0 ≤ degreeLinear 6 2 := by
    unfold degreeLinear balance
    norm_num
    linarith [gamma_bounds.1]
  have hL : degreeLinear 6 2 ≤ (10617291:ℝ)/2500000 := by
    unfold degreeLinear balance
    norm_num
    linarith [gamma_bounds.2]
  have hl : log ((2:ℝ)/6) ≤ (-274653:ℝ)/250000 := by
    rw [show (2:ℝ)/6 = ((3:ℝ)/1)⁻¹ by norm_num, log_inv]
    linarith [log_3_1_bounds.1]
  have hC : degreeConstant 6 2 ≤ (-134026361:ℝ)/150000000 := by
    unfold degreeConstant slope
    norm_num at hl ⊢
    linarith [gamma_bounds.1]
  have h := negative_quadratic_gate (gamma 6*6^4) (degreeLinear 6 2)
    (degreeConstant 6 2) ((35619021:ℝ)/6250000) ((10617291:ℝ)/2500000) ((-134026361:ℝ)/150000000) u
    (by have := gamma_positive (6:ℝ) (by norm_num); positivity)
    (by nlinarith [gamma_bounds.1]) hL0 hL hC (by norm_num) (by norm_num)
  simpa only [negativeGap, neg_mul] using h

theorem degree_3_strict (u : ℝ) (hu : 0 ≤ u) : negativeGap 6 3 u < 0 := by
  have hL0 : 0 ≤ degreeLinear 6 3 := by
    unfold degreeLinear balance
    norm_num
    linarith [gamma_bounds.1]
  have hL : degreeLinear 6 3 ≤ (171132399:ℝ)/50000000 := by
    unfold degreeLinear balance
    norm_num
    linarith [gamma_bounds.2]
  have hl : log ((3:ℝ)/6) ≤ (-693147:ℝ)/1000000 := by
    rw [show (3:ℝ)/6 = ((2:ℝ)/1)⁻¹ by norm_num, log_inv]
    linarith [log_2_1_bounds.1]
  have hC : degreeConstant 6 3 ≤ (-115779299:ℝ)/200000000 := by
    unfold degreeConstant slope
    norm_num at hl ⊢
    linarith [gamma_bounds.1]
  have h := negative_quadratic_gate (gamma 6*6^4) (degreeLinear 6 3)
    (degreeConstant 6 3) ((35619021:ℝ)/6250000) ((171132399:ℝ)/50000000) ((-115779299:ℝ)/200000000) u
    (by have := gamma_positive (6:ℝ) (by norm_num); positivity)
    (by nlinarith [gamma_bounds.1]) hL0 hL hC (by norm_num) (by norm_num)
  simpa only [negativeGap, neg_mul] using h

theorem degree_4_strict (u : ℝ) (hu : 0 ≤ u) : negativeGap 6 4 u < 0 := by
  have hL0 : 0 ≤ degreeLinear 6 4 := by
    unfold degreeLinear balance
    norm_num
    linarith [gamma_bounds.1]
  have hL : degreeLinear 6 4 ≤ (285562863:ℝ)/100000000 := by
    unfold degreeLinear balance
    norm_num
    linarith [gamma_bounds.2]
  have hl : log ((4:ℝ)/6) ≤ (-81093:ℝ)/200000 := by
    rw [show (4:ℝ)/6 = ((3:ℝ)/2)⁻¹ by norm_num, log_inv]
    linarith [log_3_2_bounds.1]
  have hC : degreeConstant 6 4 ≤ (-4584803:ℝ)/12000000 := by
    unfold degreeConstant slope
    norm_num at hl ⊢
    linarith [gamma_bounds.1]
  have h := negative_quadratic_gate (gamma 6*6^4) (degreeLinear 6 4)
    (degreeConstant 6 4) ((35619021:ℝ)/6250000) ((285562863:ℝ)/100000000) ((-4584803:ℝ)/12000000) u
    (by have := gamma_positive (6:ℝ) (by norm_num); positivity)
    (by nlinarith [gamma_bounds.1]) hL0 hL hC (by norm_num) (by norm_num)
  simpa only [negativeGap, neg_mul] using h

theorem degree_5_strict (u : ℝ) (hu : 0 ≤ u) : negativeGap 6 5 u < 0 := by
  have hL0 : 0 ≤ degreeLinear 6 5 := by
    unfold degreeLinear balance
    norm_num
    linarith [gamma_bounds.1]
  have hL : degreeLinear 6 5 ≤ (2953767033:ℝ)/1250000000 := by
    unfold degreeLinear balance
    norm_num
    linarith [gamma_bounds.2]
  have hl : log ((5:ℝ)/6) ≤ (-182321:ℝ)/1000000 := by
    rw [show (5:ℝ)/6 = ((6:ℝ)/5)⁻¹ by norm_num, log_inv]
    linarith [log_6_5_bounds.1]
  have hC : degreeConstant 6 5 ≤ (-149865203:ℝ)/600000000 := by
    unfold degreeConstant slope
    norm_num at hl ⊢
    linarith [gamma_bounds.1]
  have h := negative_quadratic_gate (gamma 6*6^4) (degreeLinear 6 5)
    (degreeConstant 6 5) ((35619021:ℝ)/6250000) ((2953767033:ℝ)/1250000000) ((-149865203:ℝ)/600000000) u
    (by have := gamma_positive (6:ℝ) (by norm_num); positivity)
    (by nlinarith [gamma_bounds.1]) hL0 hL hC (by norm_num) (by norm_num)
  simpa only [negativeGap, neg_mul] using h

theorem degree_7_strict (u : ℝ) (hu : 0 ≤ u) : negativeGap 6 7 u < 0 := by
  have hL0 : 0 ≤ degreeLinear 6 7 := by
    unfold degreeLinear balance
    norm_num
    linarith [gamma_bounds.1]
  have hL : degreeLinear 6 7 ≤ (710590599:ℝ)/490000000 := by
    unfold degreeLinear balance
    norm_num
    linarith [gamma_bounds.2]
  have hl : log ((7:ℝ)/6) ≤ (154151:ℝ)/1000000 := by
    convert log_7_6_bounds.2 using 1 <;> norm_num
  have hC : degreeConstant 6 7 ≤ (-57004909:ℝ)/600000000 := by
    unfold degreeConstant slope
    norm_num at hl ⊢
    linarith [gamma_bounds.1]
  have h := negative_quadratic_gate (gamma 6*6^4) (degreeLinear 6 7)
    (degreeConstant 6 7) ((35619021:ℝ)/6250000) ((710590599:ℝ)/490000000) ((-57004909:ℝ)/600000000) u
    (by have := gamma_positive (6:ℝ) (by norm_num); positivity)
    (by nlinarith [gamma_bounds.1]) hL0 hL hC (by norm_num) (by norm_num)
  simpa only [negativeGap, neg_mul] using h

theorem degree_8_strict (u : ℝ) (hu : 0 ≤ u) : negativeGap 6 8 u < 0 := by
  have hL0 : 0 ≤ degreeLinear 6 8 := by
    unfold degreeLinear balance
    norm_num
    linarith [gamma_bounds.1]
  have hL : degreeLinear 6 8 ≤ (403221807:ℝ)/400000000 := by
    unfold degreeLinear balance
    norm_num
    linarith [gamma_bounds.2]
  have hl : log ((8:ℝ)/6) ≤ (287683:ℝ)/1000000 := by
    convert log_4_3_bounds.2 using 1 <;> norm_num
  have hC : degreeConstant 6 8 ≤ (-15698581:ℝ)/300000000 := by
    unfold degreeConstant slope
    norm_num at hl ⊢
    linarith [gamma_bounds.1]
  have h := negative_quadratic_gate (gamma 6*6^4) (degreeLinear 6 8)
    (degreeConstant 6 8) ((35619021:ℝ)/6250000) ((403221807:ℝ)/400000000) ((-15698581:ℝ)/300000000) u
    (by have := gamma_positive (6:ℝ) (by norm_num); positivity)
    (by nlinarith [gamma_bounds.1]) hL0 hL hC (by norm_num) (by norm_num)
  simpa only [negativeGap, neg_mul] using h

theorem degree_9_strict (u : ℝ) (hu : 0 ≤ u) : negativeGap 6 9 u < 0 := by
  have hL0 : 0 ≤ degreeLinear 6 9 := by
    unfold degreeLinear balance
    norm_num
    linarith [gamma_bounds.1]
  have hL : degreeLinear 6 9 ≤ (28510469:ℝ)/50000000 := by
    unfold degreeLinear balance
    norm_num
    linarith [gamma_bounds.2]
  have hl : log ((9:ℝ)/6) ≤ (202733:ℝ)/500000 := by
    convert log_3_2_bounds.2 using 1 <;> norm_num
  have hC : degreeConstant 6 9 ≤ (-1015921:ℝ)/40000000 := by
    unfold degreeConstant slope
    norm_num at hl ⊢
    linarith [gamma_bounds.1]
  have h := negative_quadratic_gate (gamma 6*6^4) (degreeLinear 6 9)
    (degreeConstant 6 9) ((35619021:ℝ)/6250000) ((28510469:ℝ)/50000000) ((-1015921:ℝ)/40000000) u
    (by have := gamma_positive (6:ℝ) (by norm_num); positivity)
    (by nlinarith [gamma_bounds.1]) hL0 hL hC (by norm_num) (by norm_num)
  simpa only [negativeGap, neg_mul] using h

theorem degree_10_strict (u : ℝ) (hu : 0 ≤ u) : negativeGap 6 10 u < 0 := by
  have hL0 : 0 ≤ degreeLinear 6 10 := by
    unfold degreeLinear balance
    norm_num
    linarith [gamma_bounds.1]
  have hL : degreeLinear 6 10 ≤ (42195213:ℝ)/312500000 := by
    unfold degreeLinear balance
    norm_num
    linarith [gamma_bounds.2]
  have hl : log ((10:ℝ)/6) ≤ (255413:ℝ)/500000 := by
    convert log_5_3_bounds.2 using 1 <;> norm_num
  have hC : degreeConstant 6 10 ≤ (-1633567:ℝ)/150000000 := by
    unfold degreeConstant slope
    norm_num at hl ⊢
    linarith [gamma_bounds.1]
  have h := negative_quadratic_gate (gamma 6*6^4) (degreeLinear 6 10)
    (degreeConstant 6 10) ((35619021:ℝ)/6250000) ((42195213:ℝ)/312500000) ((-1633567:ℝ)/150000000) u
    (by have := gamma_positive (6:ℝ) (by norm_num); positivity)
    (by nlinarith [gamma_bounds.1]) hL0 hL hC (by norm_num) (by norm_num)
  simpa only [negativeGap, neg_mul] using h

theorem degree_11_strict (u : ℝ) (hu : 0 ≤ u) : negativeGap 6 11 u < 0 := by
  have hL : degreeLinear 6 11 ≤ 0 := by
    unfold degreeLinear balance
    norm_num
    linarith [gamma_bounds.2]
  have hl : log ((11:ℝ)/6) ≤ (75767:ℝ)/125000 := by
    convert log_11_6_bounds.2 using 1 <;> norm_num
  have hC : degreeConstant 6 11 ≤ (-3859721:ℝ)/600000000 := by
    unfold degreeConstant slope
    norm_num at hl ⊢
    linarith [gamma_bounds.1]
  have ht := mul_nonpos_of_nonpos_of_nonneg hL hu
  have hg : 0 ≤ gamma 6*6^4*u^2 := by
    have := gamma_positive (6:ℝ) (by norm_num)
    positivity
  unfold negativeGap
  nlinarith

theorem tail_strict (d u : ℝ) (hd : 12 ≤ d) (hu : 0 ≤ u) : negativeGap 6 d u < 0 := by
  apply tail_gap_negative 6 12 d u (by norm_num) (by norm_num) hd hu
  · unfold balance; norm_num; linarith [gamma_bounds.2]
  · unfold slope; norm_num; linarith [gamma_bounds.1]
  · unfold degreeLinear balance; norm_num; linarith [gamma_bounds.2]
  · unfold degreeConstant slope
    have hl := log_2_1_bounds.2
    norm_num at hl ⊢
    linarith [gamma_bounds.1]

theorem vertex_certificate (d : ℤ) (hd : 2 ≤ d) (u : ℝ) (hu : 0 ≤ u) : 0 ≤ deficit 6 d u := by
  by_cases he : d = 6
  · subst d
    rw [Int.cast_ofNat, deficit_plane_degree 6 u (by norm_num)]
    have := gamma_positive (6:ℝ) (by norm_num)
    positivity
  have hn : negativeGap 6 d u < 0 := by
    by_cases ht : 12 ≤ d
    · exact tail_strict d u (by exact_mod_cast ht) hu
    · interval_cases d <;> norm_num at * <;> first
      | exact degree_2_strict u hu
      | exact degree_3_strict u hu
      | exact degree_4_strict u hu
      | exact degree_5_strict u hu
      | exact degree_7_strict u hu
      | exact degree_8_strict u hu
      | exact degree_9_strict u hu
      | exact degree_10_strict u hu
      | exact degree_11_strict u hu
      | contradiction
  rw [negativeGap_eq_neg_deficit 6 d u (by norm_num)] at hn
  linarith

theorem peeling_margin : slope 6*(6-1) < rate 6 := by
  have hr := log_6_1_bounds.1
  have ht := log_5_1_bounds.1
  unfold slope rate planeOrder
  norm_num at hr ht ⊢
  linarith [gamma_bounds.2]

/-- Complete unrestricted density-6 exponential determinant theorem. -/
theorem determinant_total_ones (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) (hA : Binary A) :
    |(A.det:ℝ)| ≤ exp (exponent 6 n (edgeCount A)) :=
  determinant_from_vertex_certificate 6 (by norm_num) vertex_certificate peeling_margin n A hA

theorem determinant_total_6_ones (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : Binary A) (he : edgeCount A ≤ 6*(n:ℤ)) :
    |(A.det:ℝ)| ≤ exp ((n:ℝ)*rate 6) := by
  apply (determinant_total_ones n A hA).trans
  apply exp_le_exp.mpr
  unfold exponent
  have he' : (edgeCount A:ℝ)-6*(n:ℝ) ≤ 0 := by exact_mod_cast sub_nonpos.mpr he
  have hm := mul_nonpos_of_nonneg_of_nonpos (slope_pos 6 (by norm_num)).le he'
  linarith

end SparseComponent.TotalFamily.Density6
