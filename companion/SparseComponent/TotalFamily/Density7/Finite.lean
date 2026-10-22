import SparseComponent.TotalFamily.Density7.LogBounds

namespace SparseComponent.TotalFamily.Density7
open Finset Matrix Real TotalOnes
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

noncomputable def poly (x y : ℝ) : ℝ :=
  (((0:ℝ)/1)+((-2401:ℝ)/2)*gamma 7)*x^3*y^1 +
  (((0:ℝ)/1)+((-21609:ℝ)/25)*gamma 7)*x^3*y^0 +
  (((0:ℝ)/1)+((14406:ℝ)/5)*gamma 7)*x^2*y^1 +
  (((0:ℝ)/1)+((-4116:ℝ)/25)*gamma 7)*x^2*y^0 +
  (((0:ℝ)/1)+((-2401:ℝ)/2)*gamma 7)*x^1*y^3 +
  (((0:ℝ)/1)+((14406:ℝ)/5)*gamma 7)*x^1*y^2 +
  (((-49:ℝ)/6)+((-196:ℝ)/5)*gamma 7)*x^1*y^1 +
  (((1:ℝ)/6)+((-1421:ℝ)/25)*gamma 7)*x^1*y^0 +
  (((0:ℝ)/1)+((-21609:ℝ)/25)*gamma 7)*x^0*y^3 +
  (((0:ℝ)/1)+((-4116:ℝ)/25)*gamma 7)*x^0*y^2 +
  (((1:ℝ)/6)+((-1421:ℝ)/25)*gamma 7)*x^0*y^1 +
  (((5:ℝ)/42)+((13:ℝ)/1)*gamma 7)*x^0*y^0

theorem poly_identity (x y : ℝ) : polynomialModel 7 (linearAnchor 7) x y = poly x y := by
  unfold polynomialModel linearAnchor poly
  generalize gamma 7 = g
  norm_num
  ring

theorem edge_value (d c : ℝ) (hd : d ≠ 0) (hc : c ≠ 0) :
    edgeCost 7 (linearAnchor 7) d c = poly (1/d) (1/c)+(1/d)*log (7/d)+(1/c)*log (7/c) := by
  have h := edgeCost_reciprocal 7 (1/d) (1/c) (by norm_num) (one_div_ne_zero hd) (one_div_ne_zero hc) (linearAnchor 7)
  simp only [one_div_one_div] at h
  rw [h, polynomial_edge_identity 7 (1/d) (1/c) (by norm_num), poly_identity]
  simp only [div_eq_mul_inv, one_mul]

theorem edge_value_model (d c : ℝ) (hd : d ≠ 0) (hc : c ≠ 0) :
    edgeCost 7 (linearAnchor 7) d c = polynomialModel 7 (linearAnchor 7) (1/d) (1/c)+(1/d)*log (7/d)+(1/c)*log (7/c) := by
  rw [edge_value d c hd hc, poly_identity]

theorem edge_2_2 : 0 < edgeCost 7 (linearAnchor 7) 2 2 := by
  have hd := ratio_log_lower_2
  have hc := ratio_log_lower_2
  rw [edge_value_model 2 2 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/2) = ld at *
  generalize hC : log ((7:ℝ)/2) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_2_3 : 0 < edgeCost 7 (linearAnchor 7) 2 3 := by
  have hd := ratio_log_lower_2
  have hc := ratio_log_lower_3
  rw [edge_value_model 2 3 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/2) = ld at *
  generalize hC : log ((7:ℝ)/3) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_2_4 : 0 < edgeCost 7 (linearAnchor 7) 2 4 := by
  have hd := ratio_log_lower_2
  have hc := ratio_log_lower_4
  rw [edge_value_model 2 4 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/2) = ld at *
  generalize hC : log ((7:ℝ)/4) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_2_5 : 0 < edgeCost 7 (linearAnchor 7) 2 5 := by
  have hd := ratio_log_lower_2
  have hc := ratio_log_lower_5
  rw [edge_value_model 2 5 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/2) = ld at *
  generalize hC : log ((7:ℝ)/5) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_2_6 : 0 < edgeCost 7 (linearAnchor 7) 2 6 := by
  have hd := ratio_log_lower_2
  have hc := ratio_log_lower_6
  rw [edge_value_model 2 6 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/2) = ld at *
  generalize hC : log ((7:ℝ)/6) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_2_7 : 0 < edgeCost 7 (linearAnchor 7) 2 7 := by
  have hd := ratio_log_lower_2
  have hc := ratio_log_lower_7
  rw [edge_value_model 2 7 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/2) = ld at *
  generalize hC : log ((7:ℝ)/7) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_2_8 : 0 < edgeCost 7 (linearAnchor 7) 2 8 := by
  have hd := ratio_log_lower_2
  have hc := ratio_log_lower_8
  rw [edge_value_model 2 8 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/2) = ld at *
  generalize hC : log ((7:ℝ)/8) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_2_9 : 0 < edgeCost 7 (linearAnchor 7) 2 9 := by
  have hd := ratio_log_lower_2
  have hc := ratio_log_lower_9
  rw [edge_value_model 2 9 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/2) = ld at *
  generalize hC : log ((7:ℝ)/9) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_2_10 : 0 < edgeCost 7 (linearAnchor 7) 2 10 := by
  have hd := ratio_log_lower_2
  have hc := ratio_log_lower_10
  rw [edge_value_model 2 10 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/2) = ld at *
  generalize hC : log ((7:ℝ)/10) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_2_11 : 0 < edgeCost 7 (linearAnchor 7) 2 11 := by
  have hd := ratio_log_lower_2
  have hc := ratio_log_lower_11
  rw [edge_value_model 2 11 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/2) = ld at *
  generalize hC : log ((7:ℝ)/11) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_2_12 : 0 < edgeCost 7 (linearAnchor 7) 2 12 := by
  have hd := ratio_log_lower_2
  have hc := ratio_log_lower_12
  rw [edge_value_model 2 12 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/2) = ld at *
  generalize hC : log ((7:ℝ)/12) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_2_13 : 0 < edgeCost 7 (linearAnchor 7) 2 13 := by
  have hd := ratio_log_lower_2
  have hc := ratio_log_lower_13
  rw [edge_value_model 2 13 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/2) = ld at *
  generalize hC : log ((7:ℝ)/13) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_2_14 : 0 < edgeCost 7 (linearAnchor 7) 2 14 := by
  have hd := ratio_log_lower_2
  have hc := ratio_log_lower_14
  rw [edge_value_model 2 14 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/2) = ld at *
  generalize hC : log ((7:ℝ)/14) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_2_15 : 0 < edgeCost 7 (linearAnchor 7) 2 15 := by
  have hd := ratio_log_lower_2
  have hc := ratio_log_lower_15
  rw [edge_value_model 2 15 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/2) = ld at *
  generalize hC : log ((7:ℝ)/15) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_2_16 : 0 < edgeCost 7 (linearAnchor 7) 2 16 := by
  have hd := ratio_log_lower_2
  have hc := ratio_log_lower_16
  rw [edge_value_model 2 16 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/2) = ld at *
  generalize hC : log ((7:ℝ)/16) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_2_17 : 0 < edgeCost 7 (linearAnchor 7) 2 17 := by
  have hd := ratio_log_lower_2
  have hc := ratio_log_lower_17
  rw [edge_value_model 2 17 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/2) = ld at *
  generalize hC : log ((7:ℝ)/17) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_2_18 : 0 < edgeCost 7 (linearAnchor 7) 2 18 := by
  have hd := ratio_log_lower_2
  have hc := ratio_log_lower_18
  rw [edge_value_model 2 18 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/2) = ld at *
  generalize hC : log ((7:ℝ)/18) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_2_19 : 0 < edgeCost 7 (linearAnchor 7) 2 19 := by
  have hd := ratio_log_lower_2
  have hc := ratio_log_lower_19
  rw [edge_value_model 2 19 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/2) = ld at *
  generalize hC : log ((7:ℝ)/19) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_2_20 : 0 < edgeCost 7 (linearAnchor 7) 2 20 := by
  have hd := ratio_log_lower_2
  have hc := ratio_log_lower_20
  rw [edge_value_model 2 20 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/2) = ld at *
  generalize hC : log ((7:ℝ)/20) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_2_21 : 0 < edgeCost 7 (linearAnchor 7) 2 21 := by
  have hd := ratio_log_lower_2
  have hc := ratio_log_lower_21
  rw [edge_value_model 2 21 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/2) = ld at *
  generalize hC : log ((7:ℝ)/21) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_3_3 : 0 < edgeCost 7 (linearAnchor 7) 3 3 := by
  have hd := ratio_log_lower_3
  have hc := ratio_log_lower_3
  rw [edge_value_model 3 3 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/3) = ld at *
  generalize hC : log ((7:ℝ)/3) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_3_4 : 0 < edgeCost 7 (linearAnchor 7) 3 4 := by
  have hd := ratio_log_lower_3
  have hc := ratio_log_lower_4
  rw [edge_value_model 3 4 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/3) = ld at *
  generalize hC : log ((7:ℝ)/4) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_3_5 : 0 < edgeCost 7 (linearAnchor 7) 3 5 := by
  have hd := ratio_log_lower_3
  have hc := ratio_log_lower_5
  rw [edge_value_model 3 5 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/3) = ld at *
  generalize hC : log ((7:ℝ)/5) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_3_6 : 0 < edgeCost 7 (linearAnchor 7) 3 6 := by
  have hd := ratio_log_lower_3
  have hc := ratio_log_lower_6
  rw [edge_value_model 3 6 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/3) = ld at *
  generalize hC : log ((7:ℝ)/6) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_3_7 : 0 < edgeCost 7 (linearAnchor 7) 3 7 := by
  have hd := ratio_log_lower_3
  have hc := ratio_log_lower_7
  rw [edge_value_model 3 7 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/3) = ld at *
  generalize hC : log ((7:ℝ)/7) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_3_8 : 0 < edgeCost 7 (linearAnchor 7) 3 8 := by
  have hd := ratio_log_lower_3
  have hc := ratio_log_lower_8
  rw [edge_value_model 3 8 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/3) = ld at *
  generalize hC : log ((7:ℝ)/8) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_3_9 : 0 < edgeCost 7 (linearAnchor 7) 3 9 := by
  have hd := ratio_log_lower_3
  have hc := ratio_log_lower_9
  rw [edge_value_model 3 9 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/3) = ld at *
  generalize hC : log ((7:ℝ)/9) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_3_10 : 0 < edgeCost 7 (linearAnchor 7) 3 10 := by
  have hd := ratio_log_lower_3
  have hc := ratio_log_lower_10
  rw [edge_value_model 3 10 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/3) = ld at *
  generalize hC : log ((7:ℝ)/10) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_3_11 : 0 < edgeCost 7 (linearAnchor 7) 3 11 := by
  have hd := ratio_log_lower_3
  have hc := ratio_log_lower_11
  rw [edge_value_model 3 11 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/3) = ld at *
  generalize hC : log ((7:ℝ)/11) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_3_12 : 0 < edgeCost 7 (linearAnchor 7) 3 12 := by
  have hd := ratio_log_lower_3
  have hc := ratio_log_lower_12
  rw [edge_value_model 3 12 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/3) = ld at *
  generalize hC : log ((7:ℝ)/12) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_3_13 : 0 < edgeCost 7 (linearAnchor 7) 3 13 := by
  have hd := ratio_log_lower_3
  have hc := ratio_log_lower_13
  rw [edge_value_model 3 13 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/3) = ld at *
  generalize hC : log ((7:ℝ)/13) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_3_14 : 0 < edgeCost 7 (linearAnchor 7) 3 14 := by
  have hd := ratio_log_lower_3
  have hc := ratio_log_lower_14
  rw [edge_value_model 3 14 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/3) = ld at *
  generalize hC : log ((7:ℝ)/14) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_3_15 : 0 < edgeCost 7 (linearAnchor 7) 3 15 := by
  have hd := ratio_log_lower_3
  have hc := ratio_log_lower_15
  rw [edge_value_model 3 15 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/3) = ld at *
  generalize hC : log ((7:ℝ)/15) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_3_16 : 0 < edgeCost 7 (linearAnchor 7) 3 16 := by
  have hd := ratio_log_lower_3
  have hc := ratio_log_lower_16
  rw [edge_value_model 3 16 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/3) = ld at *
  generalize hC : log ((7:ℝ)/16) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_3_17 : 0 < edgeCost 7 (linearAnchor 7) 3 17 := by
  have hd := ratio_log_lower_3
  have hc := ratio_log_lower_17
  rw [edge_value_model 3 17 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/3) = ld at *
  generalize hC : log ((7:ℝ)/17) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_3_18 : 0 < edgeCost 7 (linearAnchor 7) 3 18 := by
  have hd := ratio_log_lower_3
  have hc := ratio_log_lower_18
  rw [edge_value_model 3 18 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/3) = ld at *
  generalize hC : log ((7:ℝ)/18) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_3_19 : 0 < edgeCost 7 (linearAnchor 7) 3 19 := by
  have hd := ratio_log_lower_3
  have hc := ratio_log_lower_19
  rw [edge_value_model 3 19 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/3) = ld at *
  generalize hC : log ((7:ℝ)/19) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_3_20 : 0 < edgeCost 7 (linearAnchor 7) 3 20 := by
  have hd := ratio_log_lower_3
  have hc := ratio_log_lower_20
  rw [edge_value_model 3 20 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/3) = ld at *
  generalize hC : log ((7:ℝ)/20) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_3_21 : 0 < edgeCost 7 (linearAnchor 7) 3 21 := by
  have hd := ratio_log_lower_3
  have hc := ratio_log_lower_21
  rw [edge_value_model 3 21 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/3) = ld at *
  generalize hC : log ((7:ℝ)/21) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_4_4 : 0 < edgeCost 7 (linearAnchor 7) 4 4 := by
  have hd := ratio_log_lower_4
  have hc := ratio_log_lower_4
  rw [edge_value_model 4 4 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/4) = ld at *
  generalize hC : log ((7:ℝ)/4) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_4_5 : 0 < edgeCost 7 (linearAnchor 7) 4 5 := by
  have hd := ratio_log_lower_4
  have hc := ratio_log_lower_5
  rw [edge_value_model 4 5 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/4) = ld at *
  generalize hC : log ((7:ℝ)/5) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_4_6 : 0 < edgeCost 7 (linearAnchor 7) 4 6 := by
  have hd := ratio_log_lower_4
  have hc := ratio_log_lower_6
  rw [edge_value_model 4 6 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/4) = ld at *
  generalize hC : log ((7:ℝ)/6) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_4_7 : 0 < edgeCost 7 (linearAnchor 7) 4 7 := by
  have hd := ratio_log_lower_4
  have hc := ratio_log_lower_7
  rw [edge_value_model 4 7 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/4) = ld at *
  generalize hC : log ((7:ℝ)/7) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_4_8 : 0 < edgeCost 7 (linearAnchor 7) 4 8 := by
  have hd := ratio_log_lower_4
  have hc := ratio_log_lower_8
  rw [edge_value_model 4 8 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/4) = ld at *
  generalize hC : log ((7:ℝ)/8) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_4_9 : 0 < edgeCost 7 (linearAnchor 7) 4 9 := by
  have hd := ratio_log_lower_4
  have hc := ratio_log_lower_9
  rw [edge_value_model 4 9 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/4) = ld at *
  generalize hC : log ((7:ℝ)/9) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_4_10 : 0 < edgeCost 7 (linearAnchor 7) 4 10 := by
  have hd := ratio_log_lower_4
  have hc := ratio_log_lower_10
  rw [edge_value_model 4 10 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/4) = ld at *
  generalize hC : log ((7:ℝ)/10) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_4_11 : 0 < edgeCost 7 (linearAnchor 7) 4 11 := by
  have hd := ratio_log_lower_4
  have hc := ratio_log_lower_11
  rw [edge_value_model 4 11 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/4) = ld at *
  generalize hC : log ((7:ℝ)/11) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_4_12 : 0 < edgeCost 7 (linearAnchor 7) 4 12 := by
  have hd := ratio_log_lower_4
  have hc := ratio_log_lower_12
  rw [edge_value_model 4 12 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/4) = ld at *
  generalize hC : log ((7:ℝ)/12) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_4_13 : 0 < edgeCost 7 (linearAnchor 7) 4 13 := by
  have hd := ratio_log_lower_4
  have hc := ratio_log_lower_13
  rw [edge_value_model 4 13 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/4) = ld at *
  generalize hC : log ((7:ℝ)/13) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_4_14 : 0 < edgeCost 7 (linearAnchor 7) 4 14 := by
  have hd := ratio_log_lower_4
  have hc := ratio_log_lower_14
  rw [edge_value_model 4 14 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/4) = ld at *
  generalize hC : log ((7:ℝ)/14) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_4_15 : 0 < edgeCost 7 (linearAnchor 7) 4 15 := by
  have hd := ratio_log_lower_4
  have hc := ratio_log_lower_15
  rw [edge_value_model 4 15 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/4) = ld at *
  generalize hC : log ((7:ℝ)/15) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_4_16 : 0 < edgeCost 7 (linearAnchor 7) 4 16 := by
  have hd := ratio_log_lower_4
  have hc := ratio_log_lower_16
  rw [edge_value_model 4 16 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/4) = ld at *
  generalize hC : log ((7:ℝ)/16) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_4_17 : 0 < edgeCost 7 (linearAnchor 7) 4 17 := by
  have hd := ratio_log_lower_4
  have hc := ratio_log_lower_17
  rw [edge_value_model 4 17 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/4) = ld at *
  generalize hC : log ((7:ℝ)/17) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_4_18 : 0 < edgeCost 7 (linearAnchor 7) 4 18 := by
  have hd := ratio_log_lower_4
  have hc := ratio_log_lower_18
  rw [edge_value_model 4 18 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/4) = ld at *
  generalize hC : log ((7:ℝ)/18) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_4_19 : 0 < edgeCost 7 (linearAnchor 7) 4 19 := by
  have hd := ratio_log_lower_4
  have hc := ratio_log_lower_19
  rw [edge_value_model 4 19 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/4) = ld at *
  generalize hC : log ((7:ℝ)/19) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_4_20 : 0 < edgeCost 7 (linearAnchor 7) 4 20 := by
  have hd := ratio_log_lower_4
  have hc := ratio_log_lower_20
  rw [edge_value_model 4 20 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/4) = ld at *
  generalize hC : log ((7:ℝ)/20) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_4_21 : 0 < edgeCost 7 (linearAnchor 7) 4 21 := by
  have hd := ratio_log_lower_4
  have hc := ratio_log_lower_21
  rw [edge_value_model 4 21 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/4) = ld at *
  generalize hC : log ((7:ℝ)/21) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_5_5 : 0 < edgeCost 7 (linearAnchor 7) 5 5 := by
  have hd := ratio_log_lower_5
  have hc := ratio_log_lower_5
  rw [edge_value_model 5 5 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/5) = ld at *
  generalize hC : log ((7:ℝ)/5) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_5_6 : 0 < edgeCost 7 (linearAnchor 7) 5 6 := by
  have hd := ratio_log_lower_5
  have hc := ratio_log_lower_6
  rw [edge_value_model 5 6 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/5) = ld at *
  generalize hC : log ((7:ℝ)/6) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_5_7 : 0 < edgeCost 7 (linearAnchor 7) 5 7 := by
  have hd := ratio_log_lower_5
  have hc := ratio_log_lower_7
  rw [edge_value_model 5 7 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/5) = ld at *
  generalize hC : log ((7:ℝ)/7) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_5_8 : 0 < edgeCost 7 (linearAnchor 7) 5 8 := by
  have hd := ratio_log_lower_5
  have hc := ratio_log_lower_8
  rw [edge_value_model 5 8 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/5) = ld at *
  generalize hC : log ((7:ℝ)/8) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_5_9 : 0 < edgeCost 7 (linearAnchor 7) 5 9 := by
  have hd := ratio_log_lower_5
  have hc := ratio_log_lower_9
  rw [edge_value_model 5 9 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/5) = ld at *
  generalize hC : log ((7:ℝ)/9) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_5_10 : 0 < edgeCost 7 (linearAnchor 7) 5 10 := by
  have hd := ratio_log_lower_5
  have hc := ratio_log_lower_10
  rw [edge_value_model 5 10 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/5) = ld at *
  generalize hC : log ((7:ℝ)/10) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_5_11 : 0 < edgeCost 7 (linearAnchor 7) 5 11 := by
  have hd := ratio_log_lower_5
  have hc := ratio_log_lower_11
  rw [edge_value_model 5 11 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/5) = ld at *
  generalize hC : log ((7:ℝ)/11) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_5_12 : 0 < edgeCost 7 (linearAnchor 7) 5 12 := by
  have hd := ratio_log_lower_5
  have hc := ratio_log_lower_12
  rw [edge_value_model 5 12 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/5) = ld at *
  generalize hC : log ((7:ℝ)/12) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_5_13 : 0 < edgeCost 7 (linearAnchor 7) 5 13 := by
  have hd := ratio_log_lower_5
  have hc := ratio_log_lower_13
  rw [edge_value_model 5 13 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/5) = ld at *
  generalize hC : log ((7:ℝ)/13) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_5_14 : 0 < edgeCost 7 (linearAnchor 7) 5 14 := by
  have hd := ratio_log_lower_5
  have hc := ratio_log_lower_14
  rw [edge_value_model 5 14 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/5) = ld at *
  generalize hC : log ((7:ℝ)/14) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_5_15 : 0 < edgeCost 7 (linearAnchor 7) 5 15 := by
  have hd := ratio_log_lower_5
  have hc := ratio_log_lower_15
  rw [edge_value_model 5 15 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/5) = ld at *
  generalize hC : log ((7:ℝ)/15) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_5_16 : 0 < edgeCost 7 (linearAnchor 7) 5 16 := by
  have hd := ratio_log_lower_5
  have hc := ratio_log_lower_16
  rw [edge_value_model 5 16 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/5) = ld at *
  generalize hC : log ((7:ℝ)/16) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_5_17 : 0 < edgeCost 7 (linearAnchor 7) 5 17 := by
  have hd := ratio_log_lower_5
  have hc := ratio_log_lower_17
  rw [edge_value_model 5 17 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/5) = ld at *
  generalize hC : log ((7:ℝ)/17) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_5_18 : 0 < edgeCost 7 (linearAnchor 7) 5 18 := by
  have hd := ratio_log_lower_5
  have hc := ratio_log_lower_18
  rw [edge_value_model 5 18 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/5) = ld at *
  generalize hC : log ((7:ℝ)/18) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_5_19 : 0 < edgeCost 7 (linearAnchor 7) 5 19 := by
  have hd := ratio_log_lower_5
  have hc := ratio_log_lower_19
  rw [edge_value_model 5 19 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/5) = ld at *
  generalize hC : log ((7:ℝ)/19) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_5_20 : 0 < edgeCost 7 (linearAnchor 7) 5 20 := by
  have hd := ratio_log_lower_5
  have hc := ratio_log_lower_20
  rw [edge_value_model 5 20 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/5) = ld at *
  generalize hC : log ((7:ℝ)/20) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_5_21 : 0 < edgeCost 7 (linearAnchor 7) 5 21 := by
  have hd := ratio_log_lower_5
  have hc := ratio_log_lower_21
  rw [edge_value_model 5 21 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/5) = ld at *
  generalize hC : log ((7:ℝ)/21) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_6_6 : 0 < edgeCost 7 (linearAnchor 7) 6 6 := by
  have hd := ratio_log_lower_6
  have hc := ratio_log_lower_6
  rw [edge_value_model 6 6 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/6) = ld at *
  generalize hC : log ((7:ℝ)/6) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_6_7 : 0 < edgeCost 7 (linearAnchor 7) 6 7 := by
  have hd := ratio_log_lower_6
  have hc := ratio_log_lower_7
  rw [edge_value_model 6 7 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/6) = ld at *
  generalize hC : log ((7:ℝ)/7) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_6_8 : 0 < edgeCost 7 (linearAnchor 7) 6 8 := by
  have hd := ratio_log_lower_6
  have hc := ratio_log_lower_8
  rw [edge_value_model 6 8 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/6) = ld at *
  generalize hC : log ((7:ℝ)/8) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_6_9 : 0 < edgeCost 7 (linearAnchor 7) 6 9 := by
  have hd := ratio_log_lower_6
  have hc := ratio_log_lower_9
  rw [edge_value_model 6 9 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/6) = ld at *
  generalize hC : log ((7:ℝ)/9) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_6_10 : 0 < edgeCost 7 (linearAnchor 7) 6 10 := by
  have hd := ratio_log_lower_6
  have hc := ratio_log_lower_10
  rw [edge_value_model 6 10 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/6) = ld at *
  generalize hC : log ((7:ℝ)/10) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_6_11 : 0 < edgeCost 7 (linearAnchor 7) 6 11 := by
  have hd := ratio_log_lower_6
  have hc := ratio_log_lower_11
  rw [edge_value_model 6 11 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/6) = ld at *
  generalize hC : log ((7:ℝ)/11) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_6_12 : 0 < edgeCost 7 (linearAnchor 7) 6 12 := by
  have hd := ratio_log_lower_6
  have hc := ratio_log_lower_12
  rw [edge_value_model 6 12 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/6) = ld at *
  generalize hC : log ((7:ℝ)/12) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_6_13 : 0 < edgeCost 7 (linearAnchor 7) 6 13 := by
  have hd := ratio_log_lower_6
  have hc := ratio_log_lower_13
  rw [edge_value_model 6 13 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/6) = ld at *
  generalize hC : log ((7:ℝ)/13) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_6_14 : 0 < edgeCost 7 (linearAnchor 7) 6 14 := by
  have hd := ratio_log_lower_6
  have hc := ratio_log_lower_14
  rw [edge_value_model 6 14 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/6) = ld at *
  generalize hC : log ((7:ℝ)/14) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_6_15 : 0 < edgeCost 7 (linearAnchor 7) 6 15 := by
  have hd := ratio_log_lower_6
  have hc := ratio_log_lower_15
  rw [edge_value_model 6 15 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/6) = ld at *
  generalize hC : log ((7:ℝ)/15) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_6_16 : 0 < edgeCost 7 (linearAnchor 7) 6 16 := by
  have hd := ratio_log_lower_6
  have hc := ratio_log_lower_16
  rw [edge_value_model 6 16 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/6) = ld at *
  generalize hC : log ((7:ℝ)/16) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_6_17 : 0 < edgeCost 7 (linearAnchor 7) 6 17 := by
  have hd := ratio_log_lower_6
  have hc := ratio_log_lower_17
  rw [edge_value_model 6 17 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/6) = ld at *
  generalize hC : log ((7:ℝ)/17) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_6_18 : 0 < edgeCost 7 (linearAnchor 7) 6 18 := by
  have hd := ratio_log_lower_6
  have hc := ratio_log_lower_18
  rw [edge_value_model 6 18 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/6) = ld at *
  generalize hC : log ((7:ℝ)/18) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_6_19 : 0 < edgeCost 7 (linearAnchor 7) 6 19 := by
  have hd := ratio_log_lower_6
  have hc := ratio_log_lower_19
  rw [edge_value_model 6 19 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/6) = ld at *
  generalize hC : log ((7:ℝ)/19) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_6_20 : 0 < edgeCost 7 (linearAnchor 7) 6 20 := by
  have hd := ratio_log_lower_6
  have hc := ratio_log_lower_20
  rw [edge_value_model 6 20 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/6) = ld at *
  generalize hC : log ((7:ℝ)/20) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_6_21 : 0 < edgeCost 7 (linearAnchor 7) 6 21 := by
  have hd := ratio_log_lower_6
  have hc := ratio_log_lower_21
  rw [edge_value_model 6 21 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/6) = ld at *
  generalize hC : log ((7:ℝ)/21) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_7_8 : 0 < edgeCost 7 (linearAnchor 7) 7 8 := by
  have hd := ratio_log_lower_7
  have hc := ratio_log_lower_8
  rw [edge_value_model 7 8 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/7) = ld at *
  generalize hC : log ((7:ℝ)/8) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_7_9 : 0 < edgeCost 7 (linearAnchor 7) 7 9 := by
  have hd := ratio_log_lower_7
  have hc := ratio_log_lower_9
  rw [edge_value_model 7 9 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/7) = ld at *
  generalize hC : log ((7:ℝ)/9) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_7_10 : 0 < edgeCost 7 (linearAnchor 7) 7 10 := by
  have hd := ratio_log_lower_7
  have hc := ratio_log_lower_10
  rw [edge_value_model 7 10 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/7) = ld at *
  generalize hC : log ((7:ℝ)/10) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_7_11 : 0 < edgeCost 7 (linearAnchor 7) 7 11 := by
  have hd := ratio_log_lower_7
  have hc := ratio_log_lower_11
  rw [edge_value_model 7 11 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/7) = ld at *
  generalize hC : log ((7:ℝ)/11) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_7_12 : 0 < edgeCost 7 (linearAnchor 7) 7 12 := by
  have hd := ratio_log_lower_7
  have hc := ratio_log_lower_12
  rw [edge_value_model 7 12 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/7) = ld at *
  generalize hC : log ((7:ℝ)/12) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_7_13 : 0 < edgeCost 7 (linearAnchor 7) 7 13 := by
  have hd := ratio_log_lower_7
  have hc := ratio_log_lower_13
  rw [edge_value_model 7 13 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/7) = ld at *
  generalize hC : log ((7:ℝ)/13) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_7_14 : 0 < edgeCost 7 (linearAnchor 7) 7 14 := by
  have hd := ratio_log_lower_7
  have hc := ratio_log_lower_14
  rw [edge_value_model 7 14 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/7) = ld at *
  generalize hC : log ((7:ℝ)/14) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_7_15 : 0 < edgeCost 7 (linearAnchor 7) 7 15 := by
  have hd := ratio_log_lower_7
  have hc := ratio_log_lower_15
  rw [edge_value_model 7 15 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/7) = ld at *
  generalize hC : log ((7:ℝ)/15) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_7_16 : 0 < edgeCost 7 (linearAnchor 7) 7 16 := by
  have hd := ratio_log_lower_7
  have hc := ratio_log_lower_16
  rw [edge_value_model 7 16 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/7) = ld at *
  generalize hC : log ((7:ℝ)/16) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_7_17 : 0 < edgeCost 7 (linearAnchor 7) 7 17 := by
  have hd := ratio_log_lower_7
  have hc := ratio_log_lower_17
  rw [edge_value_model 7 17 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/7) = ld at *
  generalize hC : log ((7:ℝ)/17) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_7_18 : 0 < edgeCost 7 (linearAnchor 7) 7 18 := by
  have hd := ratio_log_lower_7
  have hc := ratio_log_lower_18
  rw [edge_value_model 7 18 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/7) = ld at *
  generalize hC : log ((7:ℝ)/18) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_7_19 : 0 < edgeCost 7 (linearAnchor 7) 7 19 := by
  have hd := ratio_log_lower_7
  have hc := ratio_log_lower_19
  rw [edge_value_model 7 19 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/7) = ld at *
  generalize hC : log ((7:ℝ)/19) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_7_20 : 0 < edgeCost 7 (linearAnchor 7) 7 20 := by
  have hd := ratio_log_lower_7
  have hc := ratio_log_lower_20
  rw [edge_value_model 7 20 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/7) = ld at *
  generalize hC : log ((7:ℝ)/20) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_7_21 : 0 < edgeCost 7 (linearAnchor 7) 7 21 := by
  have hd := ratio_log_lower_7
  have hc := ratio_log_lower_21
  rw [edge_value_model 7 21 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/7) = ld at *
  generalize hC : log ((7:ℝ)/21) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_8_8 : 0 < edgeCost 7 (linearAnchor 7) 8 8 := by
  have hd := ratio_log_lower_8
  have hc := ratio_log_lower_8
  rw [edge_value_model 8 8 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/8) = ld at *
  generalize hC : log ((7:ℝ)/8) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_8_9 : 0 < edgeCost 7 (linearAnchor 7) 8 9 := by
  have hd := ratio_log_lower_8
  have hc := ratio_log_lower_9
  rw [edge_value_model 8 9 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/8) = ld at *
  generalize hC : log ((7:ℝ)/9) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_8_10 : 0 < edgeCost 7 (linearAnchor 7) 8 10 := by
  have hd := ratio_log_lower_8
  have hc := ratio_log_lower_10
  rw [edge_value_model 8 10 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/8) = ld at *
  generalize hC : log ((7:ℝ)/10) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_8_11 : 0 < edgeCost 7 (linearAnchor 7) 8 11 := by
  have hd := ratio_log_lower_8
  have hc := ratio_log_lower_11
  rw [edge_value_model 8 11 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/8) = ld at *
  generalize hC : log ((7:ℝ)/11) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_8_12 : 0 < edgeCost 7 (linearAnchor 7) 8 12 := by
  have hd := ratio_log_lower_8
  have hc := ratio_log_lower_12
  rw [edge_value_model 8 12 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/8) = ld at *
  generalize hC : log ((7:ℝ)/12) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_8_13 : 0 < edgeCost 7 (linearAnchor 7) 8 13 := by
  have hd := ratio_log_lower_8
  have hc := ratio_log_lower_13
  rw [edge_value_model 8 13 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/8) = ld at *
  generalize hC : log ((7:ℝ)/13) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_8_14 : 0 < edgeCost 7 (linearAnchor 7) 8 14 := by
  have hd := ratio_log_lower_8
  have hc := ratio_log_lower_14
  rw [edge_value_model 8 14 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/8) = ld at *
  generalize hC : log ((7:ℝ)/14) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_8_15 : 0 < edgeCost 7 (linearAnchor 7) 8 15 := by
  have hd := ratio_log_lower_8
  have hc := ratio_log_lower_15
  rw [edge_value_model 8 15 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/8) = ld at *
  generalize hC : log ((7:ℝ)/15) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_8_16 : 0 < edgeCost 7 (linearAnchor 7) 8 16 := by
  have hd := ratio_log_lower_8
  have hc := ratio_log_lower_16
  rw [edge_value_model 8 16 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/8) = ld at *
  generalize hC : log ((7:ℝ)/16) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_8_17 : 0 < edgeCost 7 (linearAnchor 7) 8 17 := by
  have hd := ratio_log_lower_8
  have hc := ratio_log_lower_17
  rw [edge_value_model 8 17 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/8) = ld at *
  generalize hC : log ((7:ℝ)/17) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_8_18 : 0 < edgeCost 7 (linearAnchor 7) 8 18 := by
  have hd := ratio_log_lower_8
  have hc := ratio_log_lower_18
  rw [edge_value_model 8 18 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/8) = ld at *
  generalize hC : log ((7:ℝ)/18) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_8_19 : 0 < edgeCost 7 (linearAnchor 7) 8 19 := by
  have hd := ratio_log_lower_8
  have hc := ratio_log_lower_19
  rw [edge_value_model 8 19 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/8) = ld at *
  generalize hC : log ((7:ℝ)/19) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_8_20 : 0 < edgeCost 7 (linearAnchor 7) 8 20 := by
  have hd := ratio_log_lower_8
  have hc := ratio_log_lower_20
  rw [edge_value_model 8 20 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/8) = ld at *
  generalize hC : log ((7:ℝ)/20) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_8_21 : 0 < edgeCost 7 (linearAnchor 7) 8 21 := by
  have hd := ratio_log_lower_8
  have hc := ratio_log_lower_21
  rw [edge_value_model 8 21 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/8) = ld at *
  generalize hC : log ((7:ℝ)/21) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_9_9 : 0 < edgeCost 7 (linearAnchor 7) 9 9 := by
  have hd := ratio_log_lower_9
  have hc := ratio_log_lower_9
  rw [edge_value_model 9 9 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/9) = ld at *
  generalize hC : log ((7:ℝ)/9) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_9_10 : 0 < edgeCost 7 (linearAnchor 7) 9 10 := by
  have hd := ratio_log_lower_9
  have hc := ratio_log_lower_10
  rw [edge_value_model 9 10 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/9) = ld at *
  generalize hC : log ((7:ℝ)/10) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_9_11 : 0 < edgeCost 7 (linearAnchor 7) 9 11 := by
  have hd := ratio_log_lower_9
  have hc := ratio_log_lower_11
  rw [edge_value_model 9 11 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/9) = ld at *
  generalize hC : log ((7:ℝ)/11) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_9_12 : 0 < edgeCost 7 (linearAnchor 7) 9 12 := by
  have hd := ratio_log_lower_9
  have hc := ratio_log_lower_12
  rw [edge_value_model 9 12 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/9) = ld at *
  generalize hC : log ((7:ℝ)/12) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_9_13 : 0 < edgeCost 7 (linearAnchor 7) 9 13 := by
  have hd := ratio_log_lower_9
  have hc := ratio_log_lower_13
  rw [edge_value_model 9 13 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/9) = ld at *
  generalize hC : log ((7:ℝ)/13) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_9_14 : 0 < edgeCost 7 (linearAnchor 7) 9 14 := by
  have hd := ratio_log_lower_9
  have hc := ratio_log_lower_14
  rw [edge_value_model 9 14 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/9) = ld at *
  generalize hC : log ((7:ℝ)/14) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_9_15 : 0 < edgeCost 7 (linearAnchor 7) 9 15 := by
  have hd := ratio_log_lower_9
  have hc := ratio_log_lower_15
  rw [edge_value_model 9 15 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/9) = ld at *
  generalize hC : log ((7:ℝ)/15) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_9_16 : 0 < edgeCost 7 (linearAnchor 7) 9 16 := by
  have hd := ratio_log_lower_9
  have hc := ratio_log_lower_16
  rw [edge_value_model 9 16 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/9) = ld at *
  generalize hC : log ((7:ℝ)/16) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_9_17 : 0 < edgeCost 7 (linearAnchor 7) 9 17 := by
  have hd := ratio_log_lower_9
  have hc := ratio_log_lower_17
  rw [edge_value_model 9 17 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/9) = ld at *
  generalize hC : log ((7:ℝ)/17) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_9_18 : 0 < edgeCost 7 (linearAnchor 7) 9 18 := by
  have hd := ratio_log_lower_9
  have hc := ratio_log_lower_18
  rw [edge_value_model 9 18 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/9) = ld at *
  generalize hC : log ((7:ℝ)/18) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_9_19 : 0 < edgeCost 7 (linearAnchor 7) 9 19 := by
  have hd := ratio_log_lower_9
  have hc := ratio_log_lower_19
  rw [edge_value_model 9 19 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/9) = ld at *
  generalize hC : log ((7:ℝ)/19) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_9_20 : 0 < edgeCost 7 (linearAnchor 7) 9 20 := by
  have hd := ratio_log_lower_9
  have hc := ratio_log_lower_20
  rw [edge_value_model 9 20 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/9) = ld at *
  generalize hC : log ((7:ℝ)/20) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_9_21 : 0 < edgeCost 7 (linearAnchor 7) 9 21 := by
  have hd := ratio_log_lower_9
  have hc := ratio_log_lower_21
  rw [edge_value_model 9 21 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/9) = ld at *
  generalize hC : log ((7:ℝ)/21) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_10_10 : 0 < edgeCost 7 (linearAnchor 7) 10 10 := by
  have hd := ratio_log_lower_10
  have hc := ratio_log_lower_10
  rw [edge_value_model 10 10 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/10) = ld at *
  generalize hC : log ((7:ℝ)/10) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_10_11 : 0 < edgeCost 7 (linearAnchor 7) 10 11 := by
  have hd := ratio_log_lower_10
  have hc := ratio_log_lower_11
  rw [edge_value_model 10 11 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/10) = ld at *
  generalize hC : log ((7:ℝ)/11) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_10_12 : 0 < edgeCost 7 (linearAnchor 7) 10 12 := by
  have hd := ratio_log_lower_10
  have hc := ratio_log_lower_12
  rw [edge_value_model 10 12 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/10) = ld at *
  generalize hC : log ((7:ℝ)/12) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_10_13 : 0 < edgeCost 7 (linearAnchor 7) 10 13 := by
  have hd := ratio_log_lower_10
  have hc := ratio_log_lower_13
  rw [edge_value_model 10 13 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/10) = ld at *
  generalize hC : log ((7:ℝ)/13) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_10_14 : 0 < edgeCost 7 (linearAnchor 7) 10 14 := by
  have hd := ratio_log_lower_10
  have hc := ratio_log_lower_14
  rw [edge_value_model 10 14 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/10) = ld at *
  generalize hC : log ((7:ℝ)/14) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_10_15 : 0 < edgeCost 7 (linearAnchor 7) 10 15 := by
  have hd := ratio_log_lower_10
  have hc := ratio_log_lower_15
  rw [edge_value_model 10 15 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/10) = ld at *
  generalize hC : log ((7:ℝ)/15) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_10_16 : 0 < edgeCost 7 (linearAnchor 7) 10 16 := by
  have hd := ratio_log_lower_10
  have hc := ratio_log_lower_16
  rw [edge_value_model 10 16 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/10) = ld at *
  generalize hC : log ((7:ℝ)/16) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_10_17 : 0 < edgeCost 7 (linearAnchor 7) 10 17 := by
  have hd := ratio_log_lower_10
  have hc := ratio_log_lower_17
  rw [edge_value_model 10 17 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/10) = ld at *
  generalize hC : log ((7:ℝ)/17) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_10_18 : 0 < edgeCost 7 (linearAnchor 7) 10 18 := by
  have hd := ratio_log_lower_10
  have hc := ratio_log_lower_18
  rw [edge_value_model 10 18 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/10) = ld at *
  generalize hC : log ((7:ℝ)/18) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_10_19 : 0 < edgeCost 7 (linearAnchor 7) 10 19 := by
  have hd := ratio_log_lower_10
  have hc := ratio_log_lower_19
  rw [edge_value_model 10 19 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/10) = ld at *
  generalize hC : log ((7:ℝ)/19) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_10_20 : 0 < edgeCost 7 (linearAnchor 7) 10 20 := by
  have hd := ratio_log_lower_10
  have hc := ratio_log_lower_20
  rw [edge_value_model 10 20 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/10) = ld at *
  generalize hC : log ((7:ℝ)/20) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_10_21 : 0 < edgeCost 7 (linearAnchor 7) 10 21 := by
  have hd := ratio_log_lower_10
  have hc := ratio_log_lower_21
  rw [edge_value_model 10 21 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/10) = ld at *
  generalize hC : log ((7:ℝ)/21) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_11_11 : 0 < edgeCost 7 (linearAnchor 7) 11 11 := by
  have hd := ratio_log_lower_11
  have hc := ratio_log_lower_11
  rw [edge_value_model 11 11 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/11) = ld at *
  generalize hC : log ((7:ℝ)/11) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_11_12 : 0 < edgeCost 7 (linearAnchor 7) 11 12 := by
  have hd := ratio_log_lower_11
  have hc := ratio_log_lower_12
  rw [edge_value_model 11 12 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/11) = ld at *
  generalize hC : log ((7:ℝ)/12) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_11_13 : 0 < edgeCost 7 (linearAnchor 7) 11 13 := by
  have hd := ratio_log_lower_11
  have hc := ratio_log_lower_13
  rw [edge_value_model 11 13 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/11) = ld at *
  generalize hC : log ((7:ℝ)/13) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_11_14 : 0 < edgeCost 7 (linearAnchor 7) 11 14 := by
  have hd := ratio_log_lower_11
  have hc := ratio_log_lower_14
  rw [edge_value_model 11 14 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/11) = ld at *
  generalize hC : log ((7:ℝ)/14) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_11_15 : 0 < edgeCost 7 (linearAnchor 7) 11 15 := by
  have hd := ratio_log_lower_11
  have hc := ratio_log_lower_15
  rw [edge_value_model 11 15 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/11) = ld at *
  generalize hC : log ((7:ℝ)/15) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_11_16 : 0 < edgeCost 7 (linearAnchor 7) 11 16 := by
  have hd := ratio_log_lower_11
  have hc := ratio_log_lower_16
  rw [edge_value_model 11 16 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/11) = ld at *
  generalize hC : log ((7:ℝ)/16) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_11_17 : 0 < edgeCost 7 (linearAnchor 7) 11 17 := by
  have hd := ratio_log_lower_11
  have hc := ratio_log_lower_17
  rw [edge_value_model 11 17 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/11) = ld at *
  generalize hC : log ((7:ℝ)/17) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_11_18 : 0 < edgeCost 7 (linearAnchor 7) 11 18 := by
  have hd := ratio_log_lower_11
  have hc := ratio_log_lower_18
  rw [edge_value_model 11 18 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/11) = ld at *
  generalize hC : log ((7:ℝ)/18) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_11_19 : 0 < edgeCost 7 (linearAnchor 7) 11 19 := by
  have hd := ratio_log_lower_11
  have hc := ratio_log_lower_19
  rw [edge_value_model 11 19 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/11) = ld at *
  generalize hC : log ((7:ℝ)/19) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_11_20 : 0 < edgeCost 7 (linearAnchor 7) 11 20 := by
  have hd := ratio_log_lower_11
  have hc := ratio_log_lower_20
  rw [edge_value_model 11 20 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/11) = ld at *
  generalize hC : log ((7:ℝ)/20) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_11_21 : 0 < edgeCost 7 (linearAnchor 7) 11 21 := by
  have hd := ratio_log_lower_11
  have hc := ratio_log_lower_21
  rw [edge_value_model 11 21 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/11) = ld at *
  generalize hC : log ((7:ℝ)/21) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_12_12 : 0 < edgeCost 7 (linearAnchor 7) 12 12 := by
  have hd := ratio_log_lower_12
  have hc := ratio_log_lower_12
  rw [edge_value_model 12 12 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/12) = ld at *
  generalize hC : log ((7:ℝ)/12) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_12_13 : 0 < edgeCost 7 (linearAnchor 7) 12 13 := by
  have hd := ratio_log_lower_12
  have hc := ratio_log_lower_13
  rw [edge_value_model 12 13 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/12) = ld at *
  generalize hC : log ((7:ℝ)/13) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_12_14 : 0 < edgeCost 7 (linearAnchor 7) 12 14 := by
  have hd := ratio_log_lower_12
  have hc := ratio_log_lower_14
  rw [edge_value_model 12 14 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/12) = ld at *
  generalize hC : log ((7:ℝ)/14) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_12_15 : 0 < edgeCost 7 (linearAnchor 7) 12 15 := by
  have hd := ratio_log_lower_12
  have hc := ratio_log_lower_15
  rw [edge_value_model 12 15 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/12) = ld at *
  generalize hC : log ((7:ℝ)/15) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_12_16 : 0 < edgeCost 7 (linearAnchor 7) 12 16 := by
  have hd := ratio_log_lower_12
  have hc := ratio_log_lower_16
  rw [edge_value_model 12 16 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/12) = ld at *
  generalize hC : log ((7:ℝ)/16) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_12_17 : 0 < edgeCost 7 (linearAnchor 7) 12 17 := by
  have hd := ratio_log_lower_12
  have hc := ratio_log_lower_17
  rw [edge_value_model 12 17 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/12) = ld at *
  generalize hC : log ((7:ℝ)/17) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_12_18 : 0 < edgeCost 7 (linearAnchor 7) 12 18 := by
  have hd := ratio_log_lower_12
  have hc := ratio_log_lower_18
  rw [edge_value_model 12 18 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/12) = ld at *
  generalize hC : log ((7:ℝ)/18) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_12_19 : 0 < edgeCost 7 (linearAnchor 7) 12 19 := by
  have hd := ratio_log_lower_12
  have hc := ratio_log_lower_19
  rw [edge_value_model 12 19 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/12) = ld at *
  generalize hC : log ((7:ℝ)/19) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_12_20 : 0 < edgeCost 7 (linearAnchor 7) 12 20 := by
  have hd := ratio_log_lower_12
  have hc := ratio_log_lower_20
  rw [edge_value_model 12 20 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/12) = ld at *
  generalize hC : log ((7:ℝ)/20) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_12_21 : 0 < edgeCost 7 (linearAnchor 7) 12 21 := by
  have hd := ratio_log_lower_12
  have hc := ratio_log_lower_21
  rw [edge_value_model 12 21 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/12) = ld at *
  generalize hC : log ((7:ℝ)/21) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_13_13 : 0 < edgeCost 7 (linearAnchor 7) 13 13 := by
  have hd := ratio_log_lower_13
  have hc := ratio_log_lower_13
  rw [edge_value_model 13 13 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/13) = ld at *
  generalize hC : log ((7:ℝ)/13) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_13_14 : 0 < edgeCost 7 (linearAnchor 7) 13 14 := by
  have hd := ratio_log_lower_13
  have hc := ratio_log_lower_14
  rw [edge_value_model 13 14 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/13) = ld at *
  generalize hC : log ((7:ℝ)/14) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_13_15 : 0 < edgeCost 7 (linearAnchor 7) 13 15 := by
  have hd := ratio_log_lower_13
  have hc := ratio_log_lower_15
  rw [edge_value_model 13 15 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/13) = ld at *
  generalize hC : log ((7:ℝ)/15) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_13_16 : 0 < edgeCost 7 (linearAnchor 7) 13 16 := by
  have hd := ratio_log_lower_13
  have hc := ratio_log_lower_16
  rw [edge_value_model 13 16 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/13) = ld at *
  generalize hC : log ((7:ℝ)/16) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_13_17 : 0 < edgeCost 7 (linearAnchor 7) 13 17 := by
  have hd := ratio_log_lower_13
  have hc := ratio_log_lower_17
  rw [edge_value_model 13 17 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/13) = ld at *
  generalize hC : log ((7:ℝ)/17) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_13_18 : 0 < edgeCost 7 (linearAnchor 7) 13 18 := by
  have hd := ratio_log_lower_13
  have hc := ratio_log_lower_18
  rw [edge_value_model 13 18 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/13) = ld at *
  generalize hC : log ((7:ℝ)/18) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_13_19 : 0 < edgeCost 7 (linearAnchor 7) 13 19 := by
  have hd := ratio_log_lower_13
  have hc := ratio_log_lower_19
  rw [edge_value_model 13 19 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/13) = ld at *
  generalize hC : log ((7:ℝ)/19) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_13_20 : 0 < edgeCost 7 (linearAnchor 7) 13 20 := by
  have hd := ratio_log_lower_13
  have hc := ratio_log_lower_20
  rw [edge_value_model 13 20 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/13) = ld at *
  generalize hC : log ((7:ℝ)/20) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_13_21 : 0 < edgeCost 7 (linearAnchor 7) 13 21 := by
  have hd := ratio_log_lower_13
  have hc := ratio_log_lower_21
  rw [edge_value_model 13 21 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/13) = ld at *
  generalize hC : log ((7:ℝ)/21) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_14_14 : 0 < edgeCost 7 (linearAnchor 7) 14 14 := by
  have hd := ratio_log_lower_14
  have hc := ratio_log_lower_14
  rw [edge_value_model 14 14 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/14) = ld at *
  generalize hC : log ((7:ℝ)/14) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_14_15 : 0 < edgeCost 7 (linearAnchor 7) 14 15 := by
  have hd := ratio_log_lower_14
  have hc := ratio_log_lower_15
  rw [edge_value_model 14 15 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/14) = ld at *
  generalize hC : log ((7:ℝ)/15) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_14_16 : 0 < edgeCost 7 (linearAnchor 7) 14 16 := by
  have hd := ratio_log_lower_14
  have hc := ratio_log_lower_16
  rw [edge_value_model 14 16 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/14) = ld at *
  generalize hC : log ((7:ℝ)/16) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_14_17 : 0 < edgeCost 7 (linearAnchor 7) 14 17 := by
  have hd := ratio_log_lower_14
  have hc := ratio_log_lower_17
  rw [edge_value_model 14 17 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/14) = ld at *
  generalize hC : log ((7:ℝ)/17) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_14_18 : 0 < edgeCost 7 (linearAnchor 7) 14 18 := by
  have hd := ratio_log_lower_14
  have hc := ratio_log_lower_18
  rw [edge_value_model 14 18 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/14) = ld at *
  generalize hC : log ((7:ℝ)/18) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_14_19 : 0 < edgeCost 7 (linearAnchor 7) 14 19 := by
  have hd := ratio_log_lower_14
  have hc := ratio_log_lower_19
  rw [edge_value_model 14 19 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/14) = ld at *
  generalize hC : log ((7:ℝ)/19) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_14_20 : 0 < edgeCost 7 (linearAnchor 7) 14 20 := by
  have hd := ratio_log_lower_14
  have hc := ratio_log_lower_20
  rw [edge_value_model 14 20 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/14) = ld at *
  generalize hC : log ((7:ℝ)/20) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_14_21 : 0 < edgeCost 7 (linearAnchor 7) 14 21 := by
  have hd := ratio_log_lower_14
  have hc := ratio_log_lower_21
  rw [edge_value_model 14 21 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/14) = ld at *
  generalize hC : log ((7:ℝ)/21) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_15_15 : 0 < edgeCost 7 (linearAnchor 7) 15 15 := by
  have hd := ratio_log_lower_15
  have hc := ratio_log_lower_15
  rw [edge_value_model 15 15 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/15) = ld at *
  generalize hC : log ((7:ℝ)/15) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_15_16 : 0 < edgeCost 7 (linearAnchor 7) 15 16 := by
  have hd := ratio_log_lower_15
  have hc := ratio_log_lower_16
  rw [edge_value_model 15 16 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/15) = ld at *
  generalize hC : log ((7:ℝ)/16) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_15_17 : 0 < edgeCost 7 (linearAnchor 7) 15 17 := by
  have hd := ratio_log_lower_15
  have hc := ratio_log_lower_17
  rw [edge_value_model 15 17 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/15) = ld at *
  generalize hC : log ((7:ℝ)/17) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_15_18 : 0 < edgeCost 7 (linearAnchor 7) 15 18 := by
  have hd := ratio_log_lower_15
  have hc := ratio_log_lower_18
  rw [edge_value_model 15 18 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/15) = ld at *
  generalize hC : log ((7:ℝ)/18) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_15_19 : 0 < edgeCost 7 (linearAnchor 7) 15 19 := by
  have hd := ratio_log_lower_15
  have hc := ratio_log_lower_19
  rw [edge_value_model 15 19 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/15) = ld at *
  generalize hC : log ((7:ℝ)/19) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_15_20 : 0 < edgeCost 7 (linearAnchor 7) 15 20 := by
  have hd := ratio_log_lower_15
  have hc := ratio_log_lower_20
  rw [edge_value_model 15 20 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/15) = ld at *
  generalize hC : log ((7:ℝ)/20) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_15_21 : 0 < edgeCost 7 (linearAnchor 7) 15 21 := by
  have hd := ratio_log_lower_15
  have hc := ratio_log_lower_21
  rw [edge_value_model 15 21 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/15) = ld at *
  generalize hC : log ((7:ℝ)/21) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_16_16 : 0 < edgeCost 7 (linearAnchor 7) 16 16 := by
  have hd := ratio_log_lower_16
  have hc := ratio_log_lower_16
  rw [edge_value_model 16 16 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/16) = ld at *
  generalize hC : log ((7:ℝ)/16) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_16_17 : 0 < edgeCost 7 (linearAnchor 7) 16 17 := by
  have hd := ratio_log_lower_16
  have hc := ratio_log_lower_17
  rw [edge_value_model 16 17 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/16) = ld at *
  generalize hC : log ((7:ℝ)/17) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_16_18 : 0 < edgeCost 7 (linearAnchor 7) 16 18 := by
  have hd := ratio_log_lower_16
  have hc := ratio_log_lower_18
  rw [edge_value_model 16 18 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/16) = ld at *
  generalize hC : log ((7:ℝ)/18) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_16_19 : 0 < edgeCost 7 (linearAnchor 7) 16 19 := by
  have hd := ratio_log_lower_16
  have hc := ratio_log_lower_19
  rw [edge_value_model 16 19 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/16) = ld at *
  generalize hC : log ((7:ℝ)/19) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_16_20 : 0 < edgeCost 7 (linearAnchor 7) 16 20 := by
  have hd := ratio_log_lower_16
  have hc := ratio_log_lower_20
  rw [edge_value_model 16 20 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/16) = ld at *
  generalize hC : log ((7:ℝ)/20) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_16_21 : 0 < edgeCost 7 (linearAnchor 7) 16 21 := by
  have hd := ratio_log_lower_16
  have hc := ratio_log_lower_21
  rw [edge_value_model 16 21 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/16) = ld at *
  generalize hC : log ((7:ℝ)/21) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_17_17 : 0 < edgeCost 7 (linearAnchor 7) 17 17 := by
  have hd := ratio_log_lower_17
  have hc := ratio_log_lower_17
  rw [edge_value_model 17 17 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/17) = ld at *
  generalize hC : log ((7:ℝ)/17) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_17_18 : 0 < edgeCost 7 (linearAnchor 7) 17 18 := by
  have hd := ratio_log_lower_17
  have hc := ratio_log_lower_18
  rw [edge_value_model 17 18 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/17) = ld at *
  generalize hC : log ((7:ℝ)/18) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_17_19 : 0 < edgeCost 7 (linearAnchor 7) 17 19 := by
  have hd := ratio_log_lower_17
  have hc := ratio_log_lower_19
  rw [edge_value_model 17 19 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/17) = ld at *
  generalize hC : log ((7:ℝ)/19) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_17_20 : 0 < edgeCost 7 (linearAnchor 7) 17 20 := by
  have hd := ratio_log_lower_17
  have hc := ratio_log_lower_20
  rw [edge_value_model 17 20 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/17) = ld at *
  generalize hC : log ((7:ℝ)/20) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_17_21 : 0 < edgeCost 7 (linearAnchor 7) 17 21 := by
  have hd := ratio_log_lower_17
  have hc := ratio_log_lower_21
  rw [edge_value_model 17 21 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/17) = ld at *
  generalize hC : log ((7:ℝ)/21) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_18_18 : 0 < edgeCost 7 (linearAnchor 7) 18 18 := by
  have hd := ratio_log_lower_18
  have hc := ratio_log_lower_18
  rw [edge_value_model 18 18 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/18) = ld at *
  generalize hC : log ((7:ℝ)/18) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_18_19 : 0 < edgeCost 7 (linearAnchor 7) 18 19 := by
  have hd := ratio_log_lower_18
  have hc := ratio_log_lower_19
  rw [edge_value_model 18 19 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/18) = ld at *
  generalize hC : log ((7:ℝ)/19) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_18_20 : 0 < edgeCost 7 (linearAnchor 7) 18 20 := by
  have hd := ratio_log_lower_18
  have hc := ratio_log_lower_20
  rw [edge_value_model 18 20 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/18) = ld at *
  generalize hC : log ((7:ℝ)/20) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_18_21 : 0 < edgeCost 7 (linearAnchor 7) 18 21 := by
  have hd := ratio_log_lower_18
  have hc := ratio_log_lower_21
  rw [edge_value_model 18 21 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/18) = ld at *
  generalize hC : log ((7:ℝ)/21) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_19_19 : 0 < edgeCost 7 (linearAnchor 7) 19 19 := by
  have hd := ratio_log_lower_19
  have hc := ratio_log_lower_19
  rw [edge_value_model 19 19 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/19) = ld at *
  generalize hC : log ((7:ℝ)/19) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_19_20 : 0 < edgeCost 7 (linearAnchor 7) 19 20 := by
  have hd := ratio_log_lower_19
  have hc := ratio_log_lower_20
  rw [edge_value_model 19 20 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/19) = ld at *
  generalize hC : log ((7:ℝ)/20) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_19_21 : 0 < edgeCost 7 (linearAnchor 7) 19 21 := by
  have hd := ratio_log_lower_19
  have hc := ratio_log_lower_21
  rw [edge_value_model 19 21 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/19) = ld at *
  generalize hC : log ((7:ℝ)/21) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_20_20 : 0 < edgeCost 7 (linearAnchor 7) 20 20 := by
  have hd := ratio_log_lower_20
  have hc := ratio_log_lower_20
  rw [edge_value_model 20 20 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/20) = ld at *
  generalize hC : log ((7:ℝ)/20) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_20_21 : 0 < edgeCost 7 (linearAnchor 7) 20 21 := by
  have hd := ratio_log_lower_20
  have hc := ratio_log_lower_21
  rw [edge_value_model 20 21 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/20) = ld at *
  generalize hC : log ((7:ℝ)/21) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem edge_21_21 : 0 < edgeCost 7 (linearAnchor 7) 21 21 := by
  have hd := ratio_log_lower_21
  have hc := ratio_log_lower_21
  rw [edge_value_model 21 21 (by norm_num) (by norm_num)]
  unfold polynomialModel linearAnchor
  have hg := gamma_bounds
  generalize hG : gamma 7 = g at *
  generalize hD : log ((7:ℝ)/21) = ld at *
  generalize hC : log ((7:ℝ)/21) = lc at *
  norm_num at hd hc hg ⊢
  linarith only [hd, hc, hg.1, hg.2]

theorem finite_row_2 (c : ℤ) (hc0 : 2 ≤ c) (hcN : c ≤ 21)
    (hn : ¬((2:ℤ)=7 ∧ c=7)) : 0 < edgeCost 7 (linearAnchor 7) 2 c := by
  interval_cases c <;> norm_num only [Int.cast_ofNat]
  · exact edge_2_2
  · exact edge_2_3
  · exact edge_2_4
  · exact edge_2_5
  · exact edge_2_6
  · exact edge_2_7
  · exact edge_2_8
  · exact edge_2_9
  · exact edge_2_10
  · exact edge_2_11
  · exact edge_2_12
  · exact edge_2_13
  · exact edge_2_14
  · exact edge_2_15
  · exact edge_2_16
  · exact edge_2_17
  · exact edge_2_18
  · exact edge_2_19
  · exact edge_2_20
  · exact edge_2_21

theorem finite_row_3 (c : ℤ) (hc0 : 2 ≤ c) (hcN : c ≤ 21)
    (hn : ¬((3:ℤ)=7 ∧ c=7)) : 0 < edgeCost 7 (linearAnchor 7) 3 c := by
  interval_cases c <;> norm_num only [Int.cast_ofNat]
  · rw [edgeCost_symm]
    exact edge_2_3
  · exact edge_3_3
  · exact edge_3_4
  · exact edge_3_5
  · exact edge_3_6
  · exact edge_3_7
  · exact edge_3_8
  · exact edge_3_9
  · exact edge_3_10
  · exact edge_3_11
  · exact edge_3_12
  · exact edge_3_13
  · exact edge_3_14
  · exact edge_3_15
  · exact edge_3_16
  · exact edge_3_17
  · exact edge_3_18
  · exact edge_3_19
  · exact edge_3_20
  · exact edge_3_21

theorem finite_row_4 (c : ℤ) (hc0 : 2 ≤ c) (hcN : c ≤ 21)
    (hn : ¬((4:ℤ)=7 ∧ c=7)) : 0 < edgeCost 7 (linearAnchor 7) 4 c := by
  interval_cases c <;> norm_num only [Int.cast_ofNat]
  · rw [edgeCost_symm]
    exact edge_2_4
  · rw [edgeCost_symm]
    exact edge_3_4
  · exact edge_4_4
  · exact edge_4_5
  · exact edge_4_6
  · exact edge_4_7
  · exact edge_4_8
  · exact edge_4_9
  · exact edge_4_10
  · exact edge_4_11
  · exact edge_4_12
  · exact edge_4_13
  · exact edge_4_14
  · exact edge_4_15
  · exact edge_4_16
  · exact edge_4_17
  · exact edge_4_18
  · exact edge_4_19
  · exact edge_4_20
  · exact edge_4_21

theorem finite_row_5 (c : ℤ) (hc0 : 2 ≤ c) (hcN : c ≤ 21)
    (hn : ¬((5:ℤ)=7 ∧ c=7)) : 0 < edgeCost 7 (linearAnchor 7) 5 c := by
  interval_cases c <;> norm_num only [Int.cast_ofNat]
  · rw [edgeCost_symm]
    exact edge_2_5
  · rw [edgeCost_symm]
    exact edge_3_5
  · rw [edgeCost_symm]
    exact edge_4_5
  · exact edge_5_5
  · exact edge_5_6
  · exact edge_5_7
  · exact edge_5_8
  · exact edge_5_9
  · exact edge_5_10
  · exact edge_5_11
  · exact edge_5_12
  · exact edge_5_13
  · exact edge_5_14
  · exact edge_5_15
  · exact edge_5_16
  · exact edge_5_17
  · exact edge_5_18
  · exact edge_5_19
  · exact edge_5_20
  · exact edge_5_21

theorem finite_row_6 (c : ℤ) (hc0 : 2 ≤ c) (hcN : c ≤ 21)
    (hn : ¬((6:ℤ)=7 ∧ c=7)) : 0 < edgeCost 7 (linearAnchor 7) 6 c := by
  interval_cases c <;> norm_num only [Int.cast_ofNat]
  · rw [edgeCost_symm]
    exact edge_2_6
  · rw [edgeCost_symm]
    exact edge_3_6
  · rw [edgeCost_symm]
    exact edge_4_6
  · rw [edgeCost_symm]
    exact edge_5_6
  · exact edge_6_6
  · exact edge_6_7
  · exact edge_6_8
  · exact edge_6_9
  · exact edge_6_10
  · exact edge_6_11
  · exact edge_6_12
  · exact edge_6_13
  · exact edge_6_14
  · exact edge_6_15
  · exact edge_6_16
  · exact edge_6_17
  · exact edge_6_18
  · exact edge_6_19
  · exact edge_6_20
  · exact edge_6_21

theorem finite_row_7 (c : ℤ) (hc0 : 2 ≤ c) (hcN : c ≤ 21)
    (hn : ¬((7:ℤ)=7 ∧ c=7)) : 0 < edgeCost 7 (linearAnchor 7) 7 c := by
  interval_cases c <;> norm_num only [Int.cast_ofNat]
  · rw [edgeCost_symm]
    exact edge_2_7
  · rw [edgeCost_symm]
    exact edge_3_7
  · rw [edgeCost_symm]
    exact edge_4_7
  · rw [edgeCost_symm]
    exact edge_5_7
  · rw [edgeCost_symm]
    exact edge_6_7
  · exact False.elim (hn ⟨rfl,rfl⟩)
  · exact edge_7_8
  · exact edge_7_9
  · exact edge_7_10
  · exact edge_7_11
  · exact edge_7_12
  · exact edge_7_13
  · exact edge_7_14
  · exact edge_7_15
  · exact edge_7_16
  · exact edge_7_17
  · exact edge_7_18
  · exact edge_7_19
  · exact edge_7_20
  · exact edge_7_21

theorem finite_row_8 (c : ℤ) (hc0 : 2 ≤ c) (hcN : c ≤ 21)
    (hn : ¬((8:ℤ)=7 ∧ c=7)) : 0 < edgeCost 7 (linearAnchor 7) 8 c := by
  interval_cases c <;> norm_num only [Int.cast_ofNat]
  · rw [edgeCost_symm]
    exact edge_2_8
  · rw [edgeCost_symm]
    exact edge_3_8
  · rw [edgeCost_symm]
    exact edge_4_8
  · rw [edgeCost_symm]
    exact edge_5_8
  · rw [edgeCost_symm]
    exact edge_6_8
  · rw [edgeCost_symm]
    exact edge_7_8
  · exact edge_8_8
  · exact edge_8_9
  · exact edge_8_10
  · exact edge_8_11
  · exact edge_8_12
  · exact edge_8_13
  · exact edge_8_14
  · exact edge_8_15
  · exact edge_8_16
  · exact edge_8_17
  · exact edge_8_18
  · exact edge_8_19
  · exact edge_8_20
  · exact edge_8_21

theorem finite_row_9 (c : ℤ) (hc0 : 2 ≤ c) (hcN : c ≤ 21)
    (hn : ¬((9:ℤ)=7 ∧ c=7)) : 0 < edgeCost 7 (linearAnchor 7) 9 c := by
  interval_cases c <;> norm_num only [Int.cast_ofNat]
  · rw [edgeCost_symm]
    exact edge_2_9
  · rw [edgeCost_symm]
    exact edge_3_9
  · rw [edgeCost_symm]
    exact edge_4_9
  · rw [edgeCost_symm]
    exact edge_5_9
  · rw [edgeCost_symm]
    exact edge_6_9
  · rw [edgeCost_symm]
    exact edge_7_9
  · rw [edgeCost_symm]
    exact edge_8_9
  · exact edge_9_9
  · exact edge_9_10
  · exact edge_9_11
  · exact edge_9_12
  · exact edge_9_13
  · exact edge_9_14
  · exact edge_9_15
  · exact edge_9_16
  · exact edge_9_17
  · exact edge_9_18
  · exact edge_9_19
  · exact edge_9_20
  · exact edge_9_21

theorem finite_row_10 (c : ℤ) (hc0 : 2 ≤ c) (hcN : c ≤ 21)
    (hn : ¬((10:ℤ)=7 ∧ c=7)) : 0 < edgeCost 7 (linearAnchor 7) 10 c := by
  interval_cases c <;> norm_num only [Int.cast_ofNat]
  · rw [edgeCost_symm]
    exact edge_2_10
  · rw [edgeCost_symm]
    exact edge_3_10
  · rw [edgeCost_symm]
    exact edge_4_10
  · rw [edgeCost_symm]
    exact edge_5_10
  · rw [edgeCost_symm]
    exact edge_6_10
  · rw [edgeCost_symm]
    exact edge_7_10
  · rw [edgeCost_symm]
    exact edge_8_10
  · rw [edgeCost_symm]
    exact edge_9_10
  · exact edge_10_10
  · exact edge_10_11
  · exact edge_10_12
  · exact edge_10_13
  · exact edge_10_14
  · exact edge_10_15
  · exact edge_10_16
  · exact edge_10_17
  · exact edge_10_18
  · exact edge_10_19
  · exact edge_10_20
  · exact edge_10_21

theorem finite_row_11 (c : ℤ) (hc0 : 2 ≤ c) (hcN : c ≤ 21)
    (hn : ¬((11:ℤ)=7 ∧ c=7)) : 0 < edgeCost 7 (linearAnchor 7) 11 c := by
  interval_cases c <;> norm_num only [Int.cast_ofNat]
  · rw [edgeCost_symm]
    exact edge_2_11
  · rw [edgeCost_symm]
    exact edge_3_11
  · rw [edgeCost_symm]
    exact edge_4_11
  · rw [edgeCost_symm]
    exact edge_5_11
  · rw [edgeCost_symm]
    exact edge_6_11
  · rw [edgeCost_symm]
    exact edge_7_11
  · rw [edgeCost_symm]
    exact edge_8_11
  · rw [edgeCost_symm]
    exact edge_9_11
  · rw [edgeCost_symm]
    exact edge_10_11
  · exact edge_11_11
  · exact edge_11_12
  · exact edge_11_13
  · exact edge_11_14
  · exact edge_11_15
  · exact edge_11_16
  · exact edge_11_17
  · exact edge_11_18
  · exact edge_11_19
  · exact edge_11_20
  · exact edge_11_21

theorem finite_row_12 (c : ℤ) (hc0 : 2 ≤ c) (hcN : c ≤ 21)
    (hn : ¬((12:ℤ)=7 ∧ c=7)) : 0 < edgeCost 7 (linearAnchor 7) 12 c := by
  interval_cases c <;> norm_num only [Int.cast_ofNat]
  · rw [edgeCost_symm]
    exact edge_2_12
  · rw [edgeCost_symm]
    exact edge_3_12
  · rw [edgeCost_symm]
    exact edge_4_12
  · rw [edgeCost_symm]
    exact edge_5_12
  · rw [edgeCost_symm]
    exact edge_6_12
  · rw [edgeCost_symm]
    exact edge_7_12
  · rw [edgeCost_symm]
    exact edge_8_12
  · rw [edgeCost_symm]
    exact edge_9_12
  · rw [edgeCost_symm]
    exact edge_10_12
  · rw [edgeCost_symm]
    exact edge_11_12
  · exact edge_12_12
  · exact edge_12_13
  · exact edge_12_14
  · exact edge_12_15
  · exact edge_12_16
  · exact edge_12_17
  · exact edge_12_18
  · exact edge_12_19
  · exact edge_12_20
  · exact edge_12_21

theorem finite_row_13 (c : ℤ) (hc0 : 2 ≤ c) (hcN : c ≤ 21)
    (hn : ¬((13:ℤ)=7 ∧ c=7)) : 0 < edgeCost 7 (linearAnchor 7) 13 c := by
  interval_cases c <;> norm_num only [Int.cast_ofNat]
  · rw [edgeCost_symm]
    exact edge_2_13
  · rw [edgeCost_symm]
    exact edge_3_13
  · rw [edgeCost_symm]
    exact edge_4_13
  · rw [edgeCost_symm]
    exact edge_5_13
  · rw [edgeCost_symm]
    exact edge_6_13
  · rw [edgeCost_symm]
    exact edge_7_13
  · rw [edgeCost_symm]
    exact edge_8_13
  · rw [edgeCost_symm]
    exact edge_9_13
  · rw [edgeCost_symm]
    exact edge_10_13
  · rw [edgeCost_symm]
    exact edge_11_13
  · rw [edgeCost_symm]
    exact edge_12_13
  · exact edge_13_13
  · exact edge_13_14
  · exact edge_13_15
  · exact edge_13_16
  · exact edge_13_17
  · exact edge_13_18
  · exact edge_13_19
  · exact edge_13_20
  · exact edge_13_21

theorem finite_row_14 (c : ℤ) (hc0 : 2 ≤ c) (hcN : c ≤ 21)
    (hn : ¬((14:ℤ)=7 ∧ c=7)) : 0 < edgeCost 7 (linearAnchor 7) 14 c := by
  interval_cases c <;> norm_num only [Int.cast_ofNat]
  · rw [edgeCost_symm]
    exact edge_2_14
  · rw [edgeCost_symm]
    exact edge_3_14
  · rw [edgeCost_symm]
    exact edge_4_14
  · rw [edgeCost_symm]
    exact edge_5_14
  · rw [edgeCost_symm]
    exact edge_6_14
  · rw [edgeCost_symm]
    exact edge_7_14
  · rw [edgeCost_symm]
    exact edge_8_14
  · rw [edgeCost_symm]
    exact edge_9_14
  · rw [edgeCost_symm]
    exact edge_10_14
  · rw [edgeCost_symm]
    exact edge_11_14
  · rw [edgeCost_symm]
    exact edge_12_14
  · rw [edgeCost_symm]
    exact edge_13_14
  · exact edge_14_14
  · exact edge_14_15
  · exact edge_14_16
  · exact edge_14_17
  · exact edge_14_18
  · exact edge_14_19
  · exact edge_14_20
  · exact edge_14_21

theorem finite_row_15 (c : ℤ) (hc0 : 2 ≤ c) (hcN : c ≤ 21)
    (hn : ¬((15:ℤ)=7 ∧ c=7)) : 0 < edgeCost 7 (linearAnchor 7) 15 c := by
  interval_cases c <;> norm_num only [Int.cast_ofNat]
  · rw [edgeCost_symm]
    exact edge_2_15
  · rw [edgeCost_symm]
    exact edge_3_15
  · rw [edgeCost_symm]
    exact edge_4_15
  · rw [edgeCost_symm]
    exact edge_5_15
  · rw [edgeCost_symm]
    exact edge_6_15
  · rw [edgeCost_symm]
    exact edge_7_15
  · rw [edgeCost_symm]
    exact edge_8_15
  · rw [edgeCost_symm]
    exact edge_9_15
  · rw [edgeCost_symm]
    exact edge_10_15
  · rw [edgeCost_symm]
    exact edge_11_15
  · rw [edgeCost_symm]
    exact edge_12_15
  · rw [edgeCost_symm]
    exact edge_13_15
  · rw [edgeCost_symm]
    exact edge_14_15
  · exact edge_15_15
  · exact edge_15_16
  · exact edge_15_17
  · exact edge_15_18
  · exact edge_15_19
  · exact edge_15_20
  · exact edge_15_21

theorem finite_row_16 (c : ℤ) (hc0 : 2 ≤ c) (hcN : c ≤ 21)
    (hn : ¬((16:ℤ)=7 ∧ c=7)) : 0 < edgeCost 7 (linearAnchor 7) 16 c := by
  interval_cases c <;> norm_num only [Int.cast_ofNat]
  · rw [edgeCost_symm]
    exact edge_2_16
  · rw [edgeCost_symm]
    exact edge_3_16
  · rw [edgeCost_symm]
    exact edge_4_16
  · rw [edgeCost_symm]
    exact edge_5_16
  · rw [edgeCost_symm]
    exact edge_6_16
  · rw [edgeCost_symm]
    exact edge_7_16
  · rw [edgeCost_symm]
    exact edge_8_16
  · rw [edgeCost_symm]
    exact edge_9_16
  · rw [edgeCost_symm]
    exact edge_10_16
  · rw [edgeCost_symm]
    exact edge_11_16
  · rw [edgeCost_symm]
    exact edge_12_16
  · rw [edgeCost_symm]
    exact edge_13_16
  · rw [edgeCost_symm]
    exact edge_14_16
  · rw [edgeCost_symm]
    exact edge_15_16
  · exact edge_16_16
  · exact edge_16_17
  · exact edge_16_18
  · exact edge_16_19
  · exact edge_16_20
  · exact edge_16_21

theorem finite_row_17 (c : ℤ) (hc0 : 2 ≤ c) (hcN : c ≤ 21)
    (hn : ¬((17:ℤ)=7 ∧ c=7)) : 0 < edgeCost 7 (linearAnchor 7) 17 c := by
  interval_cases c <;> norm_num only [Int.cast_ofNat]
  · rw [edgeCost_symm]
    exact edge_2_17
  · rw [edgeCost_symm]
    exact edge_3_17
  · rw [edgeCost_symm]
    exact edge_4_17
  · rw [edgeCost_symm]
    exact edge_5_17
  · rw [edgeCost_symm]
    exact edge_6_17
  · rw [edgeCost_symm]
    exact edge_7_17
  · rw [edgeCost_symm]
    exact edge_8_17
  · rw [edgeCost_symm]
    exact edge_9_17
  · rw [edgeCost_symm]
    exact edge_10_17
  · rw [edgeCost_symm]
    exact edge_11_17
  · rw [edgeCost_symm]
    exact edge_12_17
  · rw [edgeCost_symm]
    exact edge_13_17
  · rw [edgeCost_symm]
    exact edge_14_17
  · rw [edgeCost_symm]
    exact edge_15_17
  · rw [edgeCost_symm]
    exact edge_16_17
  · exact edge_17_17
  · exact edge_17_18
  · exact edge_17_19
  · exact edge_17_20
  · exact edge_17_21

theorem finite_row_18 (c : ℤ) (hc0 : 2 ≤ c) (hcN : c ≤ 21)
    (hn : ¬((18:ℤ)=7 ∧ c=7)) : 0 < edgeCost 7 (linearAnchor 7) 18 c := by
  interval_cases c <;> norm_num only [Int.cast_ofNat]
  · rw [edgeCost_symm]
    exact edge_2_18
  · rw [edgeCost_symm]
    exact edge_3_18
  · rw [edgeCost_symm]
    exact edge_4_18
  · rw [edgeCost_symm]
    exact edge_5_18
  · rw [edgeCost_symm]
    exact edge_6_18
  · rw [edgeCost_symm]
    exact edge_7_18
  · rw [edgeCost_symm]
    exact edge_8_18
  · rw [edgeCost_symm]
    exact edge_9_18
  · rw [edgeCost_symm]
    exact edge_10_18
  · rw [edgeCost_symm]
    exact edge_11_18
  · rw [edgeCost_symm]
    exact edge_12_18
  · rw [edgeCost_symm]
    exact edge_13_18
  · rw [edgeCost_symm]
    exact edge_14_18
  · rw [edgeCost_symm]
    exact edge_15_18
  · rw [edgeCost_symm]
    exact edge_16_18
  · rw [edgeCost_symm]
    exact edge_17_18
  · exact edge_18_18
  · exact edge_18_19
  · exact edge_18_20
  · exact edge_18_21

theorem finite_row_19 (c : ℤ) (hc0 : 2 ≤ c) (hcN : c ≤ 21)
    (hn : ¬((19:ℤ)=7 ∧ c=7)) : 0 < edgeCost 7 (linearAnchor 7) 19 c := by
  interval_cases c <;> norm_num only [Int.cast_ofNat]
  · rw [edgeCost_symm]
    exact edge_2_19
  · rw [edgeCost_symm]
    exact edge_3_19
  · rw [edgeCost_symm]
    exact edge_4_19
  · rw [edgeCost_symm]
    exact edge_5_19
  · rw [edgeCost_symm]
    exact edge_6_19
  · rw [edgeCost_symm]
    exact edge_7_19
  · rw [edgeCost_symm]
    exact edge_8_19
  · rw [edgeCost_symm]
    exact edge_9_19
  · rw [edgeCost_symm]
    exact edge_10_19
  · rw [edgeCost_symm]
    exact edge_11_19
  · rw [edgeCost_symm]
    exact edge_12_19
  · rw [edgeCost_symm]
    exact edge_13_19
  · rw [edgeCost_symm]
    exact edge_14_19
  · rw [edgeCost_symm]
    exact edge_15_19
  · rw [edgeCost_symm]
    exact edge_16_19
  · rw [edgeCost_symm]
    exact edge_17_19
  · rw [edgeCost_symm]
    exact edge_18_19
  · exact edge_19_19
  · exact edge_19_20
  · exact edge_19_21

theorem finite_row_20 (c : ℤ) (hc0 : 2 ≤ c) (hcN : c ≤ 21)
    (hn : ¬((20:ℤ)=7 ∧ c=7)) : 0 < edgeCost 7 (linearAnchor 7) 20 c := by
  interval_cases c <;> norm_num only [Int.cast_ofNat]
  · rw [edgeCost_symm]
    exact edge_2_20
  · rw [edgeCost_symm]
    exact edge_3_20
  · rw [edgeCost_symm]
    exact edge_4_20
  · rw [edgeCost_symm]
    exact edge_5_20
  · rw [edgeCost_symm]
    exact edge_6_20
  · rw [edgeCost_symm]
    exact edge_7_20
  · rw [edgeCost_symm]
    exact edge_8_20
  · rw [edgeCost_symm]
    exact edge_9_20
  · rw [edgeCost_symm]
    exact edge_10_20
  · rw [edgeCost_symm]
    exact edge_11_20
  · rw [edgeCost_symm]
    exact edge_12_20
  · rw [edgeCost_symm]
    exact edge_13_20
  · rw [edgeCost_symm]
    exact edge_14_20
  · rw [edgeCost_symm]
    exact edge_15_20
  · rw [edgeCost_symm]
    exact edge_16_20
  · rw [edgeCost_symm]
    exact edge_17_20
  · rw [edgeCost_symm]
    exact edge_18_20
  · rw [edgeCost_symm]
    exact edge_19_20
  · exact edge_20_20
  · exact edge_20_21

theorem finite_row_21 (c : ℤ) (hc0 : 2 ≤ c) (hcN : c ≤ 21)
    (hn : ¬((21:ℤ)=7 ∧ c=7)) : 0 < edgeCost 7 (linearAnchor 7) 21 c := by
  interval_cases c <;> norm_num only [Int.cast_ofNat]
  · rw [edgeCost_symm]
    exact edge_2_21
  · rw [edgeCost_symm]
    exact edge_3_21
  · rw [edgeCost_symm]
    exact edge_4_21
  · rw [edgeCost_symm]
    exact edge_5_21
  · rw [edgeCost_symm]
    exact edge_6_21
  · rw [edgeCost_symm]
    exact edge_7_21
  · rw [edgeCost_symm]
    exact edge_8_21
  · rw [edgeCost_symm]
    exact edge_9_21
  · rw [edgeCost_symm]
    exact edge_10_21
  · rw [edgeCost_symm]
    exact edge_11_21
  · rw [edgeCost_symm]
    exact edge_12_21
  · rw [edgeCost_symm]
    exact edge_13_21
  · rw [edgeCost_symm]
    exact edge_14_21
  · rw [edgeCost_symm]
    exact edge_15_21
  · rw [edgeCost_symm]
    exact edge_16_21
  · rw [edgeCost_symm]
    exact edge_17_21
  · rw [edgeCost_symm]
    exact edge_18_21
  · rw [edgeCost_symm]
    exact edge_19_21
  · rw [edgeCost_symm]
    exact edge_20_21
  · exact edge_21_21

theorem finite_strict (d c : ℤ) (hd0 : 2 ≤ d) (hc0 : 2 ≤ c)
    (hdN : d ≤ 21) (hcN : c ≤ 21) (hn : ¬(d=7 ∧ c=7)) :
    0 < edgeCost 7 (linearAnchor 7) d c := by
  interval_cases d <;> norm_num only [Int.cast_ofNat]
  · exact finite_row_2 c hc0 hcN hn
  · exact finite_row_3 c hc0 hcN hn
  · exact finite_row_4 c hc0 hcN hn
  · exact finite_row_5 c hc0 hcN hn
  · exact finite_row_6 c hc0 hcN hn
  · exact finite_row_7 c hc0 hcN hn
  · exact finite_row_8 c hc0 hcN hn
  · exact finite_row_9 c hc0 hcN hn
  · exact finite_row_10 c hc0 hcN hn
  · exact finite_row_11 c hc0 hcN hn
  · exact finite_row_12 c hc0 hcN hn
  · exact finite_row_13 c hc0 hcN hn
  · exact finite_row_14 c hc0 hcN hn
  · exact finite_row_15 c hc0 hcN hn
  · exact finite_row_16 c hc0 hcN hn
  · exact finite_row_17 c hc0 hcN hn
  · exact finite_row_18 c hc0 hcN hn
  · exact finite_row_19 c hc0 hcN hn
  · exact finite_row_20 c hc0 hcN hn
  · exact finite_row_21 c hc0 hcN hn

end SparseComponent.TotalFamily.Density7
