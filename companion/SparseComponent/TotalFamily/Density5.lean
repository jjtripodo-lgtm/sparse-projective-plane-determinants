import SparseComponent.TotalFamily.LogCertificates

namespace SparseComponent.TotalFamily.Density5
open Finset Matrix Real TotalOnes Certificates

theorem gamma_bounds : (193731:ℝ)/25000000 ≤ gamma 5 ∧ gamma 5 ≤ (30997:ℝ)/4000000 := by
  have h := log_25_4_bounds
  unfold gamma logGamma
  rw [← log_div (by norm_num : (5:ℝ)^2 ≠ 0) (by norm_num : (5:ℝ)-1 ≠ 0)]
  norm_num at h ⊢
  constructor <;> linarith

theorem degree_2_strict (u : ℝ) (hu : 0 ≤ u) : negativeGap 5 2 u < 0 := by
  have hL0 : 0 ≤ degreeLinear 5 2 := by
    unfold degreeLinear balance
    norm_num
    linarith [gamma_bounds.1]
  have hL : degreeLinear 5 2 ≤ (23561881:ℝ)/6400000 := by
    unfold degreeLinear balance
    norm_num
    linarith [gamma_bounds.2]
  have hl : log ((2:ℝ)/5) ≤ (-91629:ℝ)/100000 := by
    rw [show (2:ℝ)/5 = ((5:ℝ)/2)⁻¹ by norm_num, log_inv]
    linarith [log_5_2_bounds.1]
  have hC : degreeConstant 5 2 ≤ (-39020313:ℝ)/50000000 := by
    unfold degreeConstant slope
    norm_num at hl ⊢
    linarith [gamma_bounds.1]
  have h := negative_quadratic_gate (gamma 5*5^4) (degreeLinear 5 2)
    (degreeConstant 5 2) ((193731:ℝ)/40000) ((23561881:ℝ)/6400000) ((-39020313:ℝ)/50000000) u
    (by have := gamma_positive (5:ℝ) (by norm_num); positivity)
    (by nlinarith [gamma_bounds.1]) hL0 hL hC (by norm_num) (by norm_num)
  simpa only [negativeGap, neg_mul] using h

theorem degree_3_strict (u : ℝ) (hu : 0 ≤ u) : negativeGap 5 3 u < 0 := by
  have hL0 : 0 ≤ degreeLinear 5 3 := by
    unfold degreeLinear balance
    norm_num
    linarith [gamma_bounds.1]
  have hL : degreeLinear 5 3 ≤ (21119827:ℝ)/7200000 := by
    unfold degreeLinear balance
    norm_num
    linarith [gamma_bounds.2]
  have hl : log ((3:ℝ)/5) ≤ (-20433:ℝ)/40000 := by
    rw [show (3:ℝ)/5 = ((5:ℝ)/3)⁻¹ by norm_num, log_inv]
    linarith [log_5_3_bounds.1]
  have hC : degreeConstant 5 3 ≤ (-12120321:ℝ)/25000000 := by
    unfold degreeConstant slope
    norm_num at hl ⊢
    linarith [gamma_bounds.1]
  have h := negative_quadratic_gate (gamma 5*5^4) (degreeLinear 5 3)
    (degreeConstant 5 3) ((193731:ℝ)/40000) ((21119827:ℝ)/7200000) ((-12120321:ℝ)/25000000) u
    (by have := gamma_positive (5:ℝ) (by norm_num); positivity)
    (by nlinarith [gamma_bounds.1]) hL0 hL hC (by norm_num) (by norm_num)
  simpa only [negativeGap, neg_mul] using h

theorem degree_4_strict (u : ℝ) (hu : 0 ≤ u) : negativeGap 5 4 u < 0 := by
  have hL0 : 0 ≤ degreeLinear 5 4 := by
    unfold degreeLinear balance
    norm_num
    linarith [gamma_bounds.1]
  have hL : degreeLinear 5 4 ≤ (61534593:ℝ)/25600000 := by
    unfold degreeLinear balance
    norm_num
    linarith [gamma_bounds.2]
  have hl : log ((4:ℝ)/5) ≤ (-223143:ℝ)/1000000 := by
    rw [show (4:ℝ)/5 = ((5:ℝ)/4)⁻¹ by norm_num, log_inv]
    linarith [log_5_4_bounds.1]
  have hC : degreeConstant 5 4 ≤ (-15350121:ℝ)/50000000 := by
    unfold degreeConstant slope
    norm_num at hl ⊢
    linarith [gamma_bounds.1]
  have h := negative_quadratic_gate (gamma 5*5^4) (degreeLinear 5 4)
    (degreeConstant 5 4) ((193731:ℝ)/40000) ((61534593:ℝ)/25600000) ((-15350121:ℝ)/50000000) u
    (by have := gamma_positive (5:ℝ) (by norm_num); positivity)
    (by nlinarith [gamma_bounds.1]) hL0 hL hC (by norm_num) (by norm_num)
  simpa only [negativeGap, neg_mul] using h

theorem degree_6_strict (u : ℝ) (hu : 0 ≤ u) : negativeGap 5 6 u < 0 := by
  have hL0 : 0 ≤ degreeLinear 5 6 := by
    unfold degreeLinear balance
    norm_num
    linarith [gamma_bounds.1]
  have hL : degreeLinear 5 6 ≤ (86159177:ℝ)/57600000 := by
    unfold degreeLinear balance
    norm_num
    linarith [gamma_bounds.2]
  have hl : log ((6:ℝ)/5) ≤ (91161:ℝ)/500000 := by
    convert log_6_5_bounds.2 using 1 <;> norm_num
  have hC : degreeConstant 5 6 ≤ (-6064029:ℝ)/50000000 := by
    unfold degreeConstant slope
    norm_num at hl ⊢
    linarith [gamma_bounds.1]
  have h := negative_quadratic_gate (gamma 5*5^4) (degreeLinear 5 6)
    (degreeConstant 5 6) ((193731:ℝ)/40000) ((86159177:ℝ)/57600000) ((-6064029:ℝ)/50000000) u
    (by have := gamma_positive (5:ℝ) (by norm_num); positivity)
    (by nlinarith [gamma_bounds.1]) hL0 hL hC (by norm_num) (by norm_num)
  simpa only [negativeGap, neg_mul] using h

theorem degree_7_strict (u : ℝ) (hu : 0 ≤ u) : negativeGap 5 7 u < 0 := by
  have hL0 : 0 ≤ degreeLinear 5 7 := by
    unfold degreeLinear balance
    norm_num
    linarith [gamma_bounds.1]
  have hL : degreeLinear 5 7 ≤ (41790213:ℝ)/39200000 := by
    unfold degreeLinear balance
    norm_num
    linarith [gamma_bounds.2]
  have hl : log ((7:ℝ)/5) ≤ (336473:ℝ)/1000000 := by
    convert log_7_5_bounds.2 using 1 <;> norm_num
  have hC : degreeConstant 5 7 ≤ (-1925029:ℝ)/25000000 := by
    unfold degreeConstant slope
    norm_num at hl ⊢
    linarith [gamma_bounds.1]
  have h := negative_quadratic_gate (gamma 5*5^4) (degreeLinear 5 7)
    (degreeConstant 5 7) ((193731:ℝ)/40000) ((41790213:ℝ)/39200000) ((-1925029:ℝ)/25000000) u
    (by have := gamma_positive (5:ℝ) (by norm_num); positivity)
    (by nlinarith [gamma_bounds.1]) hL0 hL hC (by norm_num) (by norm_num)
  simpa only [negativeGap, neg_mul] using h

theorem degree_8_strict (u : ℝ) (hu : 0 ≤ u) : negativeGap 5 8 u < 0 := by
  have hL0 : 0 ≤ degreeLinear 5 8 := by
    unfold degreeLinear balance
    norm_num
    linarith [gamma_bounds.1]
  have hL : degreeLinear 5 8 ≤ (65802049:ℝ)/102400000 := by
    unfold degreeLinear balance
    norm_num
    linarith [gamma_bounds.2]
  have hl : log ((8:ℝ)/5) ≤ (117501:ℝ)/250000 := by
    convert log_8_5_bounds.2 using 1 <;> norm_num
  have hC : degreeConstant 5 8 ≤ (-2667087:ℝ)/50000000 := by
    unfold degreeConstant slope
    norm_num at hl ⊢
    linarith [gamma_bounds.1]
  have h := negative_quadratic_gate (gamma 5*5^4) (degreeLinear 5 8)
    (degreeConstant 5 8) ((193731:ℝ)/40000) ((65802049:ℝ)/102400000) ((-2667087:ℝ)/50000000) u
    (by have := gamma_positive (5:ℝ) (by norm_num); positivity)
    (by nlinarith [gamma_bounds.1]) hL0 hL hC (by norm_num) (by norm_num)
  simpa only [negativeGap, neg_mul] using h

theorem degree_9_strict (u : ℝ) (hu : 0 ≤ u) : negativeGap 5 9 u < 0 := by
  have hL0 : 0 ≤ degreeLinear 5 9 := by
    unfold degreeLinear balance
    norm_num
    linarith [gamma_bounds.1]
  have hL : degreeLinear 5 9 ≤ (3608731:ℝ)/16200000 := by
    unfold degreeLinear balance
    norm_num
    linarith [gamma_bounds.2]
  have hl : log ((9:ℝ)/5) ≤ (587787:ℝ)/1000000 := by
    convert log_9_5_bounds.2 using 1 <;> norm_num
  have hC : degreeConstant 5 9 ≤ (-567879:ℝ)/12500000 := by
    unfold degreeConstant slope
    norm_num at hl ⊢
    linarith [gamma_bounds.1]
  have h := negative_quadratic_gate (gamma 5*5^4) (degreeLinear 5 9)
    (degreeConstant 5 9) ((193731:ℝ)/40000) ((3608731:ℝ)/16200000) ((-567879:ℝ)/12500000) u
    (by have := gamma_positive (5:ℝ) (by norm_num); positivity)
    (by nlinarith [gamma_bounds.1]) hL0 hL hC (by norm_num) (by norm_num)
  simpa only [negativeGap, neg_mul] using h

theorem tail_strict (d u : ℝ) (hd : 10 ≤ d) (hu : 0 ≤ u) : negativeGap 5 d u < 0 := by
  apply tail_gap_negative 5 10 d u (by norm_num) (by norm_num) hd hu
  · unfold balance; norm_num; linarith [gamma_bounds.2]
  · unfold slope; norm_num; linarith [gamma_bounds.1]
  · unfold degreeLinear balance; norm_num; linarith [gamma_bounds.2]
  · unfold degreeConstant slope
    have hl := log_2_1_bounds.2
    norm_num at hl ⊢
    linarith [gamma_bounds.1]

theorem vertex_certificate (d : ℤ) (hd : 2 ≤ d) (u : ℝ) (hu : 0 ≤ u) : 0 ≤ deficit 5 d u := by
  by_cases he : d = 5
  · subst d
    rw [Int.cast_ofNat, deficit_plane_degree 5 u (by norm_num)]
    have := gamma_positive (5:ℝ) (by norm_num)
    positivity
  have hn : negativeGap 5 d u < 0 := by
    by_cases ht : 10 ≤ d
    · exact tail_strict d u (by exact_mod_cast ht) hu
    · interval_cases d <;> norm_num at * <;> first
      | exact degree_2_strict u hu
      | exact degree_3_strict u hu
      | exact degree_4_strict u hu
      | exact degree_6_strict u hu
      | exact degree_7_strict u hu
      | exact degree_8_strict u hu
      | exact degree_9_strict u hu
      | contradiction
  rw [negativeGap_eq_neg_deficit 5 d u (by norm_num)] at hn
  linarith

theorem peeling_margin : slope 5*(5-1) < rate 5 := by
  have hr := log_5_1_bounds.1
  have ht := log_4_1_bounds.1
  unfold slope rate planeOrder
  norm_num at hr ht ⊢
  linarith [gamma_bounds.2]

/-- Complete unrestricted density-5 exponential determinant theorem. -/
theorem determinant_total_ones (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) (hA : Binary A) :
    |(A.det:ℝ)| ≤ exp (exponent 5 n (edgeCount A)) :=
  determinant_from_vertex_certificate 5 (by norm_num) vertex_certificate peeling_margin n A hA

theorem determinant_total_5_ones (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : Binary A) (he : edgeCount A ≤ 5*(n:ℤ)) :
    |(A.det:ℝ)| ≤ exp ((n:ℝ)*rate 5) := by
  apply (determinant_total_ones n A hA).trans
  apply exp_le_exp.mpr
  unfold exponent
  have he' : (edgeCount A:ℝ)-5*(n:ℝ) ≤ 0 := by exact_mod_cast sub_nonpos.mpr he
  have hm := mul_nonpos_of_nonneg_of_nonpos (slope_pos 5 (by norm_num)).le he'
  linarith

end SparseComponent.TotalFamily.Density5
