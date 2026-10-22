import SparseComponent.TotalFamily.Density7.Finite

namespace SparseComponent.TotalFamily.Density7
open Finset Matrix Real TotalOnes
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

theorem tail_log (y : ℝ) (hy : 0 < y) (hY : y ≤ 1/22) :
    ((-114513231:ℝ)/2200000000) ≤ y*log (7*y) := by
  have hl : log ((7:ℝ)*(1/22)) ≤ -1 := by
    rw [show (7:ℝ)*(1/22) = (((22:ℝ)/7))⁻¹ by norm_num, log_inv]
    linarith [log_22_7.1]
  have h := xlog_tail_lower 7 (1/22) y (by norm_num) (by norm_num) hy hY hl
  have hb := mul_le_mul_of_nonneg_left ratio_log_lower_22 (by norm_num : (0:ℝ) ≤ 1/22)
  norm_num at h hb ⊢
  linarith

theorem mixed_2 (y : ℝ) (hy : 0 < y) (hY : y ≤ 1/22) :
    0 < poly (1/2) y+(1/2)*log (7/2)+y*log (7*y) := by
  have hy0 := hy.le
  have ht := tail_log y hy hY
  have hx := mul_le_mul_of_nonneg_left ratio_log_lower_2 (by norm_num : (0:ℝ) ≤ 1/2)
  have h0 : ((-835707064837:ℝ)/3360000000000) ≤ (((17:ℝ)/84)+((-1317:ℝ)/8)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have h1 : ((-307628299406429:ℝ)/120000000000000) ≤ (((-47:ℝ)/12)+((197519:ℝ)/400)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have p1 := nonnegative_power_bounds y (1/22) hy0 hY 1
  have b1 := monomial_lower (((-47:ℝ)/12)+((197519:ℝ)/400)*gamma 7) ((-307628299406429:ℝ)/120000000000000) (y^1) ((1/22)^1) h1 p1.1 p1.2
  norm_num at b1
  have h2 : ((8740922606997:ℝ)/2500000000000) ≤ (((0:ℝ)/1)+((31899:ℝ)/25)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have p2 := nonnegative_power_bounds y (1/22) hy0 hY 2
  have b2 := monomial_lower (((0:ℝ)/1)+((31899:ℝ)/25)*gamma 7) ((8740922606997:ℝ)/2500000000000) (y^2) ((1/22)^2) h2 p2.1 p2.2
  norm_num at b2
  have h3 : ((-8026610710601:ℝ)/2000000000000) ≤ (((0:ℝ)/1)+((-146461:ℝ)/100)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have p3 := nonnegative_power_bounds y (1/22) hy0 hY 3
  have b3 := monomial_lower (((0:ℝ)/1)+((-146461:ℝ)/100)*gamma 7) ((-8026610710601:ℝ)/2000000000000) (y^3) ((1/22)^3) h3 p3.1 p3.2
  norm_num at b3
  have he : poly (1/2) y = (((17:ℝ)/84)+((-1317:ℝ)/8)*gamma 7)*y^0 + (((-47:ℝ)/12)+((197519:ℝ)/400)*gamma 7)*y^1 + (((0:ℝ)/1)+((31899:ℝ)/25)*gamma 7)*y^2 + (((0:ℝ)/1)+((-146461:ℝ)/100)*gamma 7)*y^3 := by
    unfold poly; generalize gamma 7 = g; norm_num; ring
  rw [he]
  generalize hG : gamma 7 = g at *
  generalize hL : log ((7:ℝ)/2) = ld at *
  norm_num at hx ⊢
  linarith only [ht, hx, h0, b1, b2, b3]

theorem mixed_3 (y : ℝ) (hy : 0 < y) (hY : y ≤ 1/22) :
    0 < poly (1/3) y+(1/3)*log (7/3)+y*log (7*y) := by
  have hy0 := hy.le
  have ht := tail_log y hy hY
  have hx := mul_le_mul_of_nonneg_left ratio_log_lower_3 (by norm_num : (0:ℝ) ≤ 1/3)
  have h0 : ((644443351141:ℝ)/31500000000000) ≤ (((11:ℝ)/63)+((-4219:ℝ)/75)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have h1 : ((-268882810661957:ℝ)/135000000000000) ≤ (((-23:ℝ)/9)+((277781:ℝ)/1350)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have p1 := nonnegative_power_bounds y (1/22) hy0 hY 1
  have b1 := monomial_lower (((-23:ℝ)/9)+((277781:ℝ)/1350)*gamma 7) ((-268882810661957:ℝ)/135000000000000) (y^1) ((1/22)^1) h1 p1.1 p1.2
  norm_num at b1
  have h2 : ((2725664038741:ℝ)/1250000000000) ≤ (((0:ℝ)/1)+((19894:ℝ)/25)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have p2 := nonnegative_power_bounds y (1/22) hy0 hY 2
  have b2 := monomial_lower (((0:ℝ)/1)+((19894:ℝ)/25)*gamma 7) ((2725664038741:ℝ)/1250000000000) (y^2) ((1/22)^2) h2 p2.1 p2.2
  norm_num at b2
  have h3 : ((-10395118789139:ℝ)/3000000000000) ≤ (((0:ℝ)/1)+((-189679:ℝ)/150)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have p3 := nonnegative_power_bounds y (1/22) hy0 hY 3
  have b3 := monomial_lower (((0:ℝ)/1)+((-189679:ℝ)/150)*gamma 7) ((-10395118789139:ℝ)/3000000000000) (y^3) ((1/22)^3) h3 p3.1 p3.2
  norm_num at b3
  have he : poly (1/3) y = (((11:ℝ)/63)+((-4219:ℝ)/75)*gamma 7)*y^0 + (((-23:ℝ)/9)+((277781:ℝ)/1350)*gamma 7)*y^1 + (((0:ℝ)/1)+((19894:ℝ)/25)*gamma 7)*y^2 + (((0:ℝ)/1)+((-189679:ℝ)/150)*gamma 7)*y^3 := by
    unfold poly; generalize gamma 7 = g; norm_num; ring
  rw [he]
  generalize hG : gamma 7 = g at *
  generalize hL : log ((7:ℝ)/3) = ld at *
  norm_num at hx ⊢
  linarith only [ht, hx, h0, b1, b2, b3]

theorem mixed_4 (y : ℝ) (hy : 0 < y) (hY : y ≤ 1/22) :
    0 < poly (1/4) y+(1/4)*log (7/4)+y*log (7*y) := by
  have hy0 := hy.le
  have ht := tail_log y hy hY
  have hx := mul_le_mul_of_nonneg_left ratio_log_lower_4 (by norm_num : (0:ℝ) ≤ 1/4)
  have h0 : ((20651499884317:ℝ)/224000000000000) ≤ (((9:ℝ)/56)+((-40009:ℝ)/1600)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have h1 : ((-516981375608199:ℝ)/320000000000000) ≤ (((-15:ℝ)/8)+((302967:ℝ)/3200)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have p1 := nonnegative_power_bounds y (1/22) hy0 hY 1
  have b1 := monomial_lower (((-15:ℝ)/8)+((302967:ℝ)/3200)*gamma 7) ((-516981375608199:ℝ)/320000000000000) (y^1) ((1/22)^1) h1 p1.1 p1.2
  norm_num at b1
  have h2 : ((7613061625449:ℝ)/5000000000000) ≤ (((0:ℝ)/1)+((27783:ℝ)/50)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have p2 := nonnegative_power_bounds y (1/22) hy0 hY 2
  have b2 := monomial_lower (((0:ℝ)/1)+((27783:ℝ)/50)*gamma 7) ((7613061625449:ℝ)/5000000000000) (y^2) ((1/22)^2) h2 p2.1 p2.2
  norm_num at b2
  have h3 : ((-12763626867677:ℝ)/4000000000000) ≤ (((0:ℝ)/1)+((-232897:ℝ)/200)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have p3 := nonnegative_power_bounds y (1/22) hy0 hY 3
  have b3 := monomial_lower (((0:ℝ)/1)+((-232897:ℝ)/200)*gamma 7) ((-12763626867677:ℝ)/4000000000000) (y^3) ((1/22)^3) h3 p3.1 p3.2
  norm_num at b3
  have he : poly (1/4) y = (((9:ℝ)/56)+((-40009:ℝ)/1600)*gamma 7)*y^0 + (((-15:ℝ)/8)+((302967:ℝ)/3200)*gamma 7)*y^1 + (((0:ℝ)/1)+((27783:ℝ)/50)*gamma 7)*y^2 + (((0:ℝ)/1)+((-232897:ℝ)/200)*gamma 7)*y^3 := by
    unfold poly; generalize gamma 7 = g; norm_num; ring
  rw [he]
  generalize hG : gamma 7 = g at *
  generalize hL : log ((7:ℝ)/4) = ld at *
  norm_num at hx ⊢
  linarith only [ht, hx, h0, b1, b2, b3]

theorem mixed_5 (y : ℝ) (hy : 0 < y) (hY : y ≤ 1/22) :
    0 < poly (1/5) y+(1/5)*log (7/5)+y*log (7*y) := by
  have hy0 := hy.le
  have ht := tail_log y hy hY
  have hx := mul_le_mul_of_nonneg_left ratio_log_lower_5 (by norm_num : (0:ℝ) ≤ 1/5)
  have h0 : ((157315065051071:ℝ)/1312500000000000) ≤ (((16:ℝ)/105)+((-37089:ℝ)/3125)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have h1 : ((-101581323387731:ℝ)/75000000000000) ≤ (((-22:ℝ)/15)+((10241:ℝ)/250)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have p1 := nonnegative_power_bounds y (1/22) hy0 hY 1
  have b1 := monomial_lower (((-22:ℝ)/15)+((10241:ℝ)/250)*gamma 7) ((-101581323387731:ℝ)/75000000000000) (y^1) ((1/22)^1) h1 p1.1 p1.2
  norm_num at b1
  have h2 : ((281965245387:ℝ)/250000000000) ≤ (((0:ℝ)/1)+((2058:ℝ)/5)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have p2 := nonnegative_power_bounds y (1/22) hy0 hY 2
  have b2 := monomial_lower (((0:ℝ)/1)+((2058:ℝ)/5)*gamma 7) ((281965245387:ℝ)/250000000000) (y^2) ((1/22)^2) h2 p2.1 p2.2
  norm_num at b2
  have h3 : ((-3026426989243:ℝ)/1000000000000) ≤ (((0:ℝ)/1)+((-55223:ℝ)/50)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have p3 := nonnegative_power_bounds y (1/22) hy0 hY 3
  have b3 := monomial_lower (((0:ℝ)/1)+((-55223:ℝ)/50)*gamma 7) ((-3026426989243:ℝ)/1000000000000) (y^3) ((1/22)^3) h3 p3.1 p3.2
  norm_num at b3
  have he : poly (1/5) y = (((16:ℝ)/105)+((-37089:ℝ)/3125)*gamma 7)*y^0 + (((-22:ℝ)/15)+((10241:ℝ)/250)*gamma 7)*y^1 + (((0:ℝ)/1)+((2058:ℝ)/5)*gamma 7)*y^2 + (((0:ℝ)/1)+((-55223:ℝ)/50)*gamma 7)*y^3 := by
    unfold poly; generalize gamma 7 = g; norm_num; ring
  rw [he]
  generalize hG : gamma 7 = g at *
  generalize hL : log ((7:ℝ)/5) = ld at *
  norm_num at hx ⊢
  linarith only [ht, hx, h0, b1, b2, b3]

theorem mixed_6 (y : ℝ) (hy : 0 < y) (hY : y ≤ 1/22) :
    0 < poly (1/6) y+(1/6)*log (7/6)+y*log (7*y) := by
  have hy0 := hy.le
  have ht := tail_log y hy hY
  have hx := mul_le_mul_of_nonneg_left ratio_log_lower_6 (by norm_num : (0:ℝ) ≤ 1/6)
  have h0 : ((33513988838731:ℝ)/252000000000000) ≤ (((37:ℝ)/252)+((-3029:ℝ)/600)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have h1 : ((-1257144335454191:ℝ)/1080000000000000) ≤ (((-43:ℝ)/36)+((119903:ℝ)/10800)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have p1 := nonnegative_power_bounds y (1/22) hy0 hY 1
  have b1 := monomial_lower (((-43:ℝ)/36)+((119903:ℝ)/10800)*gamma 7) ((-1257144335454191:ℝ)/1080000000000000) (y^1) ((1/22)^1) h1 p1.1 p1.2
  norm_num at b1
  have h2 : ((2161733547967:ℝ)/2500000000000) ≤ (((0:ℝ)/1)+((7889:ℝ)/25)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have p2 := nonnegative_power_bounds y (1/22) hy0 hY 2
  have b2 := monomial_lower (((0:ℝ)/1)+((7889:ℝ)/25)*gamma 7) ((2161733547967:ℝ)/2500000000000) (y^2) ((1/22)^2) h2 p2.1 p2.2
  norm_num at b2
  have h3 : ((-17500643024753:ℝ)/6000000000000) ≤ (((0:ℝ)/1)+((-319333:ℝ)/300)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have p3 := nonnegative_power_bounds y (1/22) hy0 hY 3
  have b3 := monomial_lower (((0:ℝ)/1)+((-319333:ℝ)/300)*gamma 7) ((-17500643024753:ℝ)/6000000000000) (y^3) ((1/22)^3) h3 p3.1 p3.2
  norm_num at b3
  have he : poly (1/6) y = (((37:ℝ)/252)+((-3029:ℝ)/600)*gamma 7)*y^0 + (((-43:ℝ)/36)+((119903:ℝ)/10800)*gamma 7)*y^1 + (((0:ℝ)/1)+((7889:ℝ)/25)*gamma 7)*y^2 + (((0:ℝ)/1)+((-319333:ℝ)/300)*gamma 7)*y^3 := by
    unfold poly; generalize gamma 7 = g; norm_num; ring
  rw [he]
  generalize hG : gamma 7 = g at *
  generalize hL : log ((7:ℝ)/6) = ld at *
  norm_num at hx ⊢
  linarith only [ht, hx, h0, b1, b2, b3]

theorem mixed_7 (y : ℝ) (hy : 0 < y) (hY : y ≤ 1/22) :
    0 < poly (1/7) y+(1/7)*log (7/7)+y*log (7*y) := by
  have hy0 := hy.le
  have ht := tail_log y hy hY
  have hx := mul_le_mul_of_nonneg_left ratio_log_lower_7 (by norm_num : (0:ℝ) ≤ 1/7)
  have h0 : ((19616373813:ℝ)/140000000000) ≤ (((1:ℝ)/7)+((-1:ℝ)/1)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have h1 : ((-1019564935537:ℝ)/1000000000000) ≤ (((-1:ℝ)/1)+((-357:ℝ)/50)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have p1 := nonnegative_power_bounds y (1/22) hy0 hY 1
  have b1 := monomial_lower (((-1:ℝ)/1)+((-357:ℝ)/50)*gamma 7) ((-1019564935537:ℝ)/1000000000000) (y^1) ((1/22)^1) h1 p1.1 p1.2
  norm_num at b1
  have h2 : ((845895736161:ℝ)/1250000000000) ≤ (((0:ℝ)/1)+((6174:ℝ)/25)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have p2 := nonnegative_power_bounds y (1/22) hy0 hY 2
  have b2 := monomial_lower (((0:ℝ)/1)+((6174:ℝ)/25)*gamma 7) ((845895736161:ℝ)/1250000000000) (y^2) ((1/22)^2) h2 p2.1 p2.2
  norm_num at b2
  have h3 : ((-2838450157613:ℝ)/1000000000000) ≤ (((0:ℝ)/1)+((-51793:ℝ)/50)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have p3 := nonnegative_power_bounds y (1/22) hy0 hY 3
  have b3 := monomial_lower (((0:ℝ)/1)+((-51793:ℝ)/50)*gamma 7) ((-2838450157613:ℝ)/1000000000000) (y^3) ((1/22)^3) h3 p3.1 p3.2
  norm_num at b3
  have he : poly (1/7) y = (((1:ℝ)/7)+((-1:ℝ)/1)*gamma 7)*y^0 + (((-1:ℝ)/1)+((-357:ℝ)/50)*gamma 7)*y^1 + (((0:ℝ)/1)+((6174:ℝ)/25)*gamma 7)*y^2 + (((0:ℝ)/1)+((-51793:ℝ)/50)*gamma 7)*y^3 := by
    unfold poly; generalize gamma 7 = g; norm_num; ring
  rw [he]
  generalize hG : gamma 7 = g at *
  generalize hL : log ((7:ℝ)/7) = ld at *
  norm_num at hx ⊢
  linarith only [ht, hx, h0, b1, b2, b3]

theorem mixed_8 (y : ℝ) (hy : 0 < y) (hY : y ≤ 1/22) :
    0 < poly (1/8) y+(1/8)*log (7/8)+y*log (7*y) := by
  have hy0 := hy.le
  have ht := tail_log y hy hY
  have hx := mul_le_mul_of_nonneg_left ratio_log_lower_8 (by norm_num : (0:ℝ) ≤ 1/8)
  have h0 : ((3880376142209197:ℝ)/26880000000000000) ≤ (((47:ℝ)/336)+((20919:ℝ)/12800)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have h1 : ((-1392247309422847:ℝ)/1536000000000000) ≤ (((-41:ℝ)/48)+((-488089:ℝ)/25600)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have p1 := nonnegative_power_bounds y (1/22) hy0 hY 1
  have b1 := monomial_lower (((-41:ℝ)/48)+((-488089:ℝ)/25600)*gamma 7) ((-1392247309422847:ℝ)/1536000000000000) (y^1) ((1/22)^1) h1 p1.1 p1.2
  norm_num at b1
  have h2 : ((5357339662353:ℝ)/10000000000000) ≤ (((0:ℝ)/1)+((19551:ℝ)/100)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have p2 := nonnegative_power_bounds y (1/22) hy0 hY 2
  have b2 := monomial_lower (((0:ℝ)/1)+((19551:ℝ)/100)*gamma 7) ((5357339662353:ℝ)/10000000000000) (y^2) ((1/22)^2) h2 p2.1 p2.2
  norm_num at b2
  have h3 : ((-22237659181829:ℝ)/8000000000000) ≤ (((0:ℝ)/1)+((-405769:ℝ)/400)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have p3 := nonnegative_power_bounds y (1/22) hy0 hY 3
  have b3 := monomial_lower (((0:ℝ)/1)+((-405769:ℝ)/400)*gamma 7) ((-22237659181829:ℝ)/8000000000000) (y^3) ((1/22)^3) h3 p3.1 p3.2
  norm_num at b3
  have he : poly (1/8) y = (((47:ℝ)/336)+((20919:ℝ)/12800)*gamma 7)*y^0 + (((-41:ℝ)/48)+((-488089:ℝ)/25600)*gamma 7)*y^1 + (((0:ℝ)/1)+((19551:ℝ)/100)*gamma 7)*y^2 + (((0:ℝ)/1)+((-405769:ℝ)/400)*gamma 7)*y^3 := by
    unfold poly; generalize gamma 7 = g; norm_num; ring
  rw [he]
  generalize hG : gamma 7 = g at *
  generalize hL : log ((7:ℝ)/8) = ld at *
  norm_num at hx ⊢
  linarith only [ht, hx, h0, b1, b2, b3]

theorem mixed_9 (y : ℝ) (hy : 0 < y) (hY : y ≤ 1/22) :
    0 < poly (1/9) y+(1/9)*log (7/9)+y*log (7*y) := by
  have hy0 := hy.le
  have ht := tail_log y hy hY
  have hx := mul_le_mul_of_nonneg_left ratio_log_lower_9 (by norm_num : (0:ℝ) ≤ 1/9)
  have h0 : ((208463360934499:ℝ)/1417500000000000) ≤ (((26:ℝ)/189)+((7019:ℝ)/2025)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have h1 : ((-594478371189683:ℝ)/729000000000000) ≤ (((-20:ℝ)/27)+((-994063:ℝ)/36450)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have p1 := nonnegative_power_bounds y (1/22) hy0 hY 1
  have b1 := monomial_lower (((-20:ℝ)/27)+((-994063:ℝ)/36450)*gamma 7) ((-594478371189683:ℝ)/729000000000000) (y^1) ((1/22)^1) h1 p1.1 p1.2
  norm_num at b1
  have h2 : ((1597803057193:ℝ)/3750000000000) ≤ (((0:ℝ)/1)+((11662:ℝ)/75)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have p2 := nonnegative_power_bounds y (1/22) hy0 hY 2
  have b2 := monomial_lower (((0:ℝ)/1)+((11662:ℝ)/75)*gamma 7) ((1597803057193:ℝ)/3750000000000) (y^2) ((1/22)^2) h2 p2.1 p2.2
  norm_num at b2
  have h3 : ((-24606167260367:ℝ)/9000000000000) ≤ (((0:ℝ)/1)+((-448987:ℝ)/450)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have p3 := nonnegative_power_bounds y (1/22) hy0 hY 3
  have b3 := monomial_lower (((0:ℝ)/1)+((-448987:ℝ)/450)*gamma 7) ((-24606167260367:ℝ)/9000000000000) (y^3) ((1/22)^3) h3 p3.1 p3.2
  norm_num at b3
  have he : poly (1/9) y = (((26:ℝ)/189)+((7019:ℝ)/2025)*gamma 7)*y^0 + (((-20:ℝ)/27)+((-994063:ℝ)/36450)*gamma 7)*y^1 + (((0:ℝ)/1)+((11662:ℝ)/75)*gamma 7)*y^2 + (((0:ℝ)/1)+((-448987:ℝ)/450)*gamma 7)*y^3 := by
    unfold poly; generalize gamma 7 = g; norm_num; ring
  rw [he]
  generalize hG : gamma 7 = g at *
  generalize hL : log ((7:ℝ)/9) = ld at *
  norm_num at hx ⊢
  linarith only [ht, hx, h0, b1, b2, b3]

theorem mixed_10 (y : ℝ) (hy : 0 < y) (hY : y ≤ 1/22) :
    0 < poly (1/10) y+(1/10)*log (7/10)+y*log (7*y) := by
  have hy0 := hy.le
  have ht := tail_log y hy hY
  have hx := mul_le_mul_of_nonneg_left ratio_log_lower_10 (by norm_num : (0:ℝ) ≤ 1/10)
  have h0 : ((2605426985670651:ℝ)/17500000000000000) ≤ (((19:ℝ)/140)+((120131:ℝ)/25000)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have h1 : ((-29633323617077:ℝ)/40000000000000) ≤ (((-13:ℝ)/20)+((-66297:ℝ)/2000)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have p1 := nonnegative_power_bounds y (1/22) hy0 hY 1
  have b1 := monomial_lower (((-13:ℝ)/20)+((-66297:ℝ)/2000)*gamma 7) ((-29633323617077:ℝ)/40000000000000) (y^1) ((1/22)^1) h1 p1.1 p1.2
  norm_num at b1
  have h2 : ((845895736161:ℝ)/2500000000000) ≤ (((0:ℝ)/1)+((3087:ℝ)/25)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have p2 := nonnegative_power_bounds y (1/22) hy0 hY 2
  have b2 := monomial_lower (((0:ℝ)/1)+((3087:ℝ)/25)*gamma 7) ((845895736161:ℝ)/2500000000000) (y^2) ((1/22)^2) h2 p2.1 p2.2
  norm_num at b2
  have h3 : ((-5394935067781:ℝ)/2000000000000) ≤ (((0:ℝ)/1)+((-98441:ℝ)/100)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have p3 := nonnegative_power_bounds y (1/22) hy0 hY 3
  have b3 := monomial_lower (((0:ℝ)/1)+((-98441:ℝ)/100)*gamma 7) ((-5394935067781:ℝ)/2000000000000) (y^3) ((1/22)^3) h3 p3.1 p3.2
  norm_num at b3
  have he : poly (1/10) y = (((19:ℝ)/140)+((120131:ℝ)/25000)*gamma 7)*y^0 + (((-13:ℝ)/20)+((-66297:ℝ)/2000)*gamma 7)*y^1 + (((0:ℝ)/1)+((3087:ℝ)/25)*gamma 7)*y^2 + (((0:ℝ)/1)+((-98441:ℝ)/100)*gamma 7)*y^3 := by
    unfold poly; generalize gamma 7 = g; norm_num; ring
  rw [he]
  generalize hG : gamma 7 = g at *
  generalize hL : log ((7:ℝ)/10) = ld at *
  norm_num at hx ⊢
  linarith only [ht, hx, h0, b1, b2, b3]

theorem mixed_11 (y : ℝ) (hy : 0 < y) (hY : y ≤ 1/22) :
    0 < poly (1/11) y+(1/11)*log (7/11)+y*log (7*y) := by
  have hy0 := hy.le
  have ht := tail_log y hy hY
  have hx := mul_le_mul_of_nonneg_left ratio_log_lower_11 (by norm_num : (0:ℝ) ≤ 1/11)
  have h0 : ((10492407843438487:ℝ)/69877500000000000) ≤ (((31:ℝ)/231)+((193749:ℝ)/33275)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have h1 : ((-2709243322732621:ℝ)/3993000000000000) ≤ (((-19:ℝ)/33)+((-2495227:ℝ)/66550)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have p1 := nonnegative_power_bounds y (1/22) hy0 hY 1
  have b1 := monomial_lower (((-19:ℝ)/33)+((-2495227:ℝ)/66550)*gamma 7) ((-2709243322732621:ℝ)/3993000000000000) (y^1) ((1/22)^1) h1 p1.1 p1.2
  norm_num at b1
  have h2 : ((3665548190031:ℝ)/13750000000000) ≤ (((0:ℝ)/1)+((26754:ℝ)/275)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have p2 := nonnegative_power_bounds y (1/22) hy0 hY 2
  have b2 := monomial_lower (((0:ℝ)/1)+((26754:ℝ)/275)*gamma 7) ((3665548190031:ℝ)/13750000000000) (y^2) ((1/22)^2) h2 p2.1 p2.2
  norm_num at b2
  have h3 : ((-29343183417443:ℝ)/11000000000000) ≤ (((0:ℝ)/1)+((-535423:ℝ)/550)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have p3 := nonnegative_power_bounds y (1/22) hy0 hY 3
  have b3 := monomial_lower (((0:ℝ)/1)+((-535423:ℝ)/550)*gamma 7) ((-29343183417443:ℝ)/11000000000000) (y^3) ((1/22)^3) h3 p3.1 p3.2
  norm_num at b3
  have he : poly (1/11) y = (((31:ℝ)/231)+((193749:ℝ)/33275)*gamma 7)*y^0 + (((-19:ℝ)/33)+((-2495227:ℝ)/66550)*gamma 7)*y^1 + (((0:ℝ)/1)+((26754:ℝ)/275)*gamma 7)*y^2 + (((0:ℝ)/1)+((-535423:ℝ)/550)*gamma 7)*y^3 := by
    unfold poly; generalize gamma 7 = g; norm_num; ring
  rw [he]
  generalize hG : gamma 7 = g at *
  generalize hL : log ((7:ℝ)/11) = ld at *
  norm_num at hx ⊢
  linarith only [ht, hx, h0, b1, b2, b3]

theorem mixed_12 (y : ℝ) (hy : 0 < y) (hY : y ≤ 1/22) :
    0 < poly (1/12) y+(1/12)*log (7/12)+y*log (7*y) := by
  have hy0 := hy.le
  have ht := tail_log y hy hY
  have hx := mul_le_mul_of_nonneg_left ratio_log_lower_12 (by norm_num : (0:ℝ) ≤ 1/12)
  have h0 : ((60913833201773:ℝ)/403200000000000) ≤ (((67:ℝ)/504)+((1271:ℝ)/192)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have h1 : ((-1081156936033061:ℝ)/1728000000000000) ≤ (((-37:ℝ)/72)+((-3524521:ℝ)/86400)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have p1 := nonnegative_power_bounds y (1/22) hy0 hY 1
  have b1 := monomial_lower (((-37:ℝ)/72)+((-3524521:ℝ)/86400)*gamma 7) ((-1081156936033061:ℝ)/1728000000000000) (y^1) ((1/22)^1) h1 p1.1 p1.2
  norm_num at b1
  have h2 : ((1033872566419:ℝ)/5000000000000) ≤ (((0:ℝ)/1)+((3773:ℝ)/50)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have p2 := nonnegative_power_bounds y (1/22) hy0 hY 2
  have b2 := monomial_lower (((0:ℝ)/1)+((3773:ℝ)/50)*gamma 7) ((1033872566419:ℝ)/5000000000000) (y^2) ((1/22)^2) h2 p2.1 p2.2
  norm_num at b2
  have h3 : ((-31711691495981:ℝ)/12000000000000) ≤ (((0:ℝ)/1)+((-578641:ℝ)/600)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have p3 := nonnegative_power_bounds y (1/22) hy0 hY 3
  have b3 := monomial_lower (((0:ℝ)/1)+((-578641:ℝ)/600)*gamma 7) ((-31711691495981:ℝ)/12000000000000) (y^3) ((1/22)^3) h3 p3.1 p3.2
  norm_num at b3
  have he : poly (1/12) y = (((67:ℝ)/504)+((1271:ℝ)/192)*gamma 7)*y^0 + (((-37:ℝ)/72)+((-3524521:ℝ)/86400)*gamma 7)*y^1 + (((0:ℝ)/1)+((3773:ℝ)/50)*gamma 7)*y^2 + (((0:ℝ)/1)+((-578641:ℝ)/600)*gamma 7)*y^3 := by
    unfold poly; generalize gamma 7 = g; norm_num; ring
  rw [he]
  generalize hG : gamma 7 = g at *
  generalize hL : log ((7:ℝ)/12) = ld at *
  norm_num at hx ⊢
  linarith only [ht, hx, h0, b1, b2, b3]

theorem mixed_13 (y : ℝ) (hy : 0 < y) (hY : y ≤ 1/22) :
    0 < poly (1/13) y+(1/13)*log (7/13)+y*log (7*y) := by
  have hy0 := hy.le
  have ht := tail_log y hy hY
  have hx := mul_le_mul_of_nonneg_left ratio_log_lower_13 (by norm_num : (0:ℝ) ≤ 1/13)
  have h0 : ((5834871967927039:ℝ)/38447500000000000) ≤ (((12:ℝ)/91)+((398759:ℝ)/54925)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have h1 : ((-1274995089185019:ℝ)/2197000000000000) ≤ (((-6:ℝ)/13)+((-4762359:ℝ)/109850)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have p1 := nonnegative_power_bounds y (1/22) hy0 hY 1
  have b1 := monomial_lower (((-6:ℝ)/13)+((-4762359:ℝ)/109850)*gamma 7) ((-1274995089185019:ℝ)/2197000000000000) (y^1) ((1/22)^1) h1 p1.1 p1.2
  norm_num at b1
  have h2 : ((2537687208483:ℝ)/16250000000000) ≤ (((0:ℝ)/1)+((18522:ℝ)/325)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have p2 := nonnegative_power_bounds y (1/22) hy0 hY 2
  have b2 := monomial_lower (((0:ℝ)/1)+((18522:ℝ)/325)*gamma 7) ((2537687208483:ℝ)/16250000000000) (y^2) ((1/22)^2) h2 p2.1 p2.2
  norm_num at b2
  have h3 : ((-34080199574519:ℝ)/13000000000000) ≤ (((0:ℝ)/1)+((-621859:ℝ)/650)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have p3 := nonnegative_power_bounds y (1/22) hy0 hY 3
  have b3 := monomial_lower (((0:ℝ)/1)+((-621859:ℝ)/650)*gamma 7) ((-34080199574519:ℝ)/13000000000000) (y^3) ((1/22)^3) h3 p3.1 p3.2
  norm_num at b3
  have he : poly (1/13) y = (((12:ℝ)/91)+((398759:ℝ)/54925)*gamma 7)*y^0 + (((-6:ℝ)/13)+((-4762359:ℝ)/109850)*gamma 7)*y^1 + (((0:ℝ)/1)+((18522:ℝ)/325)*gamma 7)*y^2 + (((0:ℝ)/1)+((-621859:ℝ)/650)*gamma 7)*y^3 := by
    unfold poly; generalize gamma 7 = g; norm_num; ring
  rw [he]
  generalize hG : gamma 7 = g at *
  generalize hL : log ((7:ℝ)/13) = ld at *
  norm_num at hx ⊢
  linarith only [ht, hx, h0, b1, b2, b3]

theorem mixed_14 (y : ℝ) (hy : 0 < y) (hY : y ≤ 1/22) :
    0 < poly (1/14) y+(1/14)*log (7/14)+y*log (7*y) := by
  have hy0 := hy.le
  have ht := tail_log y hy hY
  have hx := mul_le_mul_of_nonneg_left ratio_log_lower_14 (by norm_num : (0:ℝ) ≤ 1/14)
  have h0 : ((63959589531991:ℝ)/420000000000000) ≤ (((11:ℝ)/84)+((1557:ℝ)/200)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have h1 : ((-12984228108673:ℝ)/24000000000000) ≤ (((-5:ℝ)/12)+((-18151:ℝ)/400)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have p1 := nonnegative_power_bounds y (1/22) hy0 hY 1
  have b1 := monomial_lower (((-5:ℝ)/12)+((-18151:ℝ)/400)*gamma 7) ((-12984228108673:ℝ)/24000000000000) (y^1) ((1/22)^1) h1 p1.1 p1.2
  norm_num at b1
  have h2 : ((281965245387:ℝ)/2500000000000) ≤ (((0:ℝ)/1)+((1029:ℝ)/25)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have p2 := nonnegative_power_bounds y (1/22) hy0 hY 2
  have b2 := monomial_lower (((0:ℝ)/1)+((1029:ℝ)/25)*gamma 7) ((281965245387:ℝ)/2500000000000) (y^2) ((1/22)^2) h2 p2.1 p2.2
  norm_num at b2
  have h3 : ((-5206958236151:ℝ)/2000000000000) ≤ (((0:ℝ)/1)+((-95011:ℝ)/100)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have p3 := nonnegative_power_bounds y (1/22) hy0 hY 3
  have b3 := monomial_lower (((0:ℝ)/1)+((-95011:ℝ)/100)*gamma 7) ((-5206958236151:ℝ)/2000000000000) (y^3) ((1/22)^3) h3 p3.1 p3.2
  norm_num at b3
  have he : poly (1/14) y = (((11:ℝ)/84)+((1557:ℝ)/200)*gamma 7)*y^0 + (((-5:ℝ)/12)+((-18151:ℝ)/400)*gamma 7)*y^1 + (((0:ℝ)/1)+((1029:ℝ)/25)*gamma 7)*y^2 + (((0:ℝ)/1)+((-95011:ℝ)/100)*gamma 7)*y^3 := by
    unfold poly; generalize gamma 7 = g; norm_num; ring
  rw [he]
  generalize hG : gamma 7 = g at *
  generalize hL : log ((7:ℝ)/14) = ld at *
  norm_num at hx ⊢
  linarith only [ht, hx, h0, b1, b2, b3]

theorem mixed_15 (y : ℝ) (hy : 0 < y) (hY : y ≤ 1/22) :
    0 < poly (1/15) y+(1/15)*log (7/15)+y*log (7*y) := by
  have hy0 := hy.le
  have ht := tail_log y hy hY
  have hx := mul_le_mul_of_nonneg_left ratio_log_lower_15 (by norm_num : (0:ℝ) ≤ 1/15)
  have h0 : ((3006100383706907:ℝ)/19687500000000000) ≤ (((41:ℝ)/315)+((77089:ℝ)/9375)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have h1 : ((-2735514277031:ℝ)/5400000000000) ≤ (((-17:ℝ)/45)+((-12691:ℝ)/270)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have p1 := nonnegative_power_bounds y (1/22) hy0 hY 1
  have b1 := monomial_lower (((-17:ℝ)/45)+((-12691:ℝ)/270)*gamma 7) ((-2735514277031:ℝ)/5400000000000) (y^1) ((1/22)^1) h1 p1.1 p1.2
  norm_num at b1
  have h2 : ((93988415129:ℝ)/1250000000000) ≤ (((0:ℝ)/1)+((686:ℝ)/25)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have p2 := nonnegative_power_bounds y (1/22) hy0 hY 2
  have b2 := monomial_lower (((0:ℝ)/1)+((686:ℝ)/25)*gamma 7) ((93988415129:ℝ)/1250000000000) (y^2) ((1/22)^2) h2 p2.1 p2.2
  norm_num at b2
  have h3 : ((-7763443146319:ℝ)/3000000000000) ≤ (((0:ℝ)/1)+((-141659:ℝ)/150)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have p3 := nonnegative_power_bounds y (1/22) hy0 hY 3
  have b3 := monomial_lower (((0:ℝ)/1)+((-141659:ℝ)/150)*gamma 7) ((-7763443146319:ℝ)/3000000000000) (y^3) ((1/22)^3) h3 p3.1 p3.2
  norm_num at b3
  have he : poly (1/15) y = (((41:ℝ)/315)+((77089:ℝ)/9375)*gamma 7)*y^0 + (((-17:ℝ)/45)+((-12691:ℝ)/270)*gamma 7)*y^1 + (((0:ℝ)/1)+((686:ℝ)/25)*gamma 7)*y^2 + (((0:ℝ)/1)+((-141659:ℝ)/150)*gamma 7)*y^3 := by
    unfold poly; generalize gamma 7 = g; norm_num; ring
  rw [he]
  generalize hG : gamma 7 = g at *
  generalize hL : log ((7:ℝ)/15) = ld at *
  norm_num at hx ⊢
  linarith only [ht, hx, h0, b1, b2, b3]

theorem mixed_16 (y : ℝ) (hy : 0 < y) (hY : y ≤ 1/22) :
    0 < poly (1/16) y+(1/16)*log (7/16)+y*log (7*y) := by
  have hy0 := hy.le
  have ht := tail_log y hy hY
  have hx := mul_le_mul_of_nonneg_left ratio_log_lower_16 (by norm_num : (0:ℝ) ≤ 1/16)
  have h0 : ((10967876567112239:ℝ)/71680000000000000) ≤ (((29:ℝ)/224)+((879959:ℝ)/102400)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have h1 : ((-1950428630734837:ℝ)/4096000000000000) ≤ (((-11:ℝ)/32)+((-9897657:ℝ)/204800)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have p1 := nonnegative_power_bounds y (1/22) hy0 hY 1
  have b1 := monomial_lower (((-11:ℝ)/32)+((-9897657:ℝ)/204800)*gamma 7) ((-1950428630734837:ℝ)/4096000000000000) (y^1) ((1/22)^1) h1 p1.1 p1.2
  norm_num at b1
  have h2 : ((845895736161:ℝ)/20000000000000) ≤ (((0:ℝ)/1)+((3087:ℝ)/200)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have p2 := nonnegative_power_bounds y (1/22) hy0 hY 2
  have b2 := monomial_lower (((0:ℝ)/1)+((3087:ℝ)/200)*gamma 7) ((845895736161:ℝ)/20000000000000) (y^2) ((1/22)^2) h2 p2.1 p2.2
  norm_num at b2
  have h3 : ((-41185723810133:ℝ)/16000000000000) ≤ (((0:ℝ)/1)+((-751513:ℝ)/800)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have p3 := nonnegative_power_bounds y (1/22) hy0 hY 3
  have b3 := monomial_lower (((0:ℝ)/1)+((-751513:ℝ)/800)*gamma 7) ((-41185723810133:ℝ)/16000000000000) (y^3) ((1/22)^3) h3 p3.1 p3.2
  norm_num at b3
  have he : poly (1/16) y = (((29:ℝ)/224)+((879959:ℝ)/102400)*gamma 7)*y^0 + (((-11:ℝ)/32)+((-9897657:ℝ)/204800)*gamma 7)*y^1 + (((0:ℝ)/1)+((3087:ℝ)/200)*gamma 7)*y^2 + (((0:ℝ)/1)+((-751513:ℝ)/800)*gamma 7)*y^3 := by
    unfold poly; generalize gamma 7 = g; norm_num; ring
  rw [he]
  generalize hG : gamma 7 = g at *
  generalize hL : log ((7:ℝ)/16) = ld at *
  norm_num at hx ⊢
  linarith only [ht, hx, h0, b1, b2, b3]

theorem mixed_17 (y : ℝ) (hy : 0 < y) (hY : y ≤ 1/22) :
    0 < poly (1/17) y+(1/17)*log (7/17)+y*log (7*y) := by
  have hy0 := hy.le
  have ht := tail_log y hy hY
  have hx := mul_le_mul_of_nonneg_left ratio_log_lower_17 (by norm_num : (0:ℝ) ≤ 1/17)
  have h0 : ((1581321560771377:ℝ)/10317300000000000) ≤ (((46:ℝ)/357)+((43779:ℝ)/4913)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have h1 : ((-6619983649763593:ℝ)/14739000000000000) ≤ (((-16:ℝ)/51)+((-12140191:ℝ)/245650)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have p1 := nonnegative_power_bounds y (1/22) hy0 hY 1
  have b1 := monomial_lower (((-16:ℝ)/51)+((-12140191:ℝ)/245650)*gamma 7) ((-6619983649763593:ℝ)/14739000000000000) (y^1) ((1/22)^1) h1 p1.1 p1.2
  norm_num at b1
  have h2 : ((281965245387:ℝ)/21250000000000) ≤ (((0:ℝ)/1)+((2058:ℝ)/425)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have p2 := nonnegative_power_bounds y (1/22) hy0 hY 2
  have b2 := monomial_lower (((0:ℝ)/1)+((2058:ℝ)/425)*gamma 7) ((281965245387:ℝ)/21250000000000) (y^2) ((1/22)^2) h2 p2.1 p2.2
  norm_num at b2
  have h3 : ((-43554231888671:ℝ)/17000000000000) ≤ (((0:ℝ)/1)+((-794731:ℝ)/850)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have p3 := nonnegative_power_bounds y (1/22) hy0 hY 3
  have b3 := monomial_lower (((0:ℝ)/1)+((-794731:ℝ)/850)*gamma 7) ((-43554231888671:ℝ)/17000000000000) (y^3) ((1/22)^3) h3 p3.1 p3.2
  norm_num at b3
  have he : poly (1/17) y = (((46:ℝ)/357)+((43779:ℝ)/4913)*gamma 7)*y^0 + (((-16:ℝ)/51)+((-12140191:ℝ)/245650)*gamma 7)*y^1 + (((0:ℝ)/1)+((2058:ℝ)/425)*gamma 7)*y^2 + (((0:ℝ)/1)+((-794731:ℝ)/850)*gamma 7)*y^3 := by
    unfold poly; generalize gamma 7 = g; norm_num; ring
  rw [he]
  generalize hG : gamma 7 = g at *
  generalize hL : log ((7:ℝ)/17) = ld at *
  norm_num at hx ⊢
  linarith only [ht, hx, h0, b1, b2, b3]

theorem mixed_18 (y : ℝ) (hy : 0 < y) (hY : y ≤ 1/22) :
    0 < poly (1/18) y+(1/18)*log (7/18)+y*log (7*y) := by
  have hy0 := hy.le
  have ht := tail_log y hy hY
  have hx := mul_le_mul_of_nonneg_left ratio_log_lower_18 (by norm_num : (0:ℝ) ≤ 1/18)
  have h0 : ((1740438980484931:ℝ)/11340000000000000) ≤ (((97:ℝ)/756)+((148811:ℝ)/16200)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have h1 : ((-2478328694094989:ℝ)/5832000000000000) ≤ (((-31:ℝ)/108)+((-14676529:ℝ)/291600)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have p1 := nonnegative_power_bounds y (1/22) hy0 hY 1
  have b1 := monomial_lower (((-31:ℝ)/108)+((-14676529:ℝ)/291600)*gamma 7) ((-2478328694094989:ℝ)/5832000000000000) (y^1) ((1/22)^1) h1 p1.1 p1.2
  norm_num at b1
  have h2 : ((-18797683163:ℝ)/1500000000000) ≤ (((0:ℝ)/1)+((-343:ℝ)/75)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have p2 := nonnegative_power_bounds y (1/22) hy0 hY 2
  have b2 := monomial_lower (((0:ℝ)/1)+((-343:ℝ)/75)*gamma 7) ((-18797683163:ℝ)/1500000000000) (y^2) ((1/22)^2) h2 p2.1 p2.2
  norm_num at b2
  have h3 : ((-45922739967209:ℝ)/18000000000000) ≤ (((0:ℝ)/1)+((-837949:ℝ)/900)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have p3 := nonnegative_power_bounds y (1/22) hy0 hY 3
  have b3 := monomial_lower (((0:ℝ)/1)+((-837949:ℝ)/900)*gamma 7) ((-45922739967209:ℝ)/18000000000000) (y^3) ((1/22)^3) h3 p3.1 p3.2
  norm_num at b3
  have he : poly (1/18) y = (((97:ℝ)/756)+((148811:ℝ)/16200)*gamma 7)*y^0 + (((-31:ℝ)/108)+((-14676529:ℝ)/291600)*gamma 7)*y^1 + (((0:ℝ)/1)+((-343:ℝ)/75)*gamma 7)*y^2 + (((0:ℝ)/1)+((-837949:ℝ)/900)*gamma 7)*y^3 := by
    unfold poly; generalize gamma 7 = g; norm_num; ring
  rw [he]
  generalize hG : gamma 7 = g at *
  generalize hL : log ((7:ℝ)/18) = ld at *
  norm_num at hx ⊢
  linarith only [ht, hx, h0, b1, b2, b3]

theorem mixed_19 (y : ℝ) (hy : 0 < y) (hY : y ≤ 1/22) :
    0 < poly (1/19) y+(1/19)*log (7/19)+y*log (7*y) := by
  have hy0 := hy.le
  have ht := tail_log y hy hY
  have hx := mul_le_mul_of_nonneg_left ratio_log_lower_19 (by norm_num : (0:ℝ) ≤ 1/19)
  have h0 : ((970680546116679:ℝ)/6317500000000000) ≤ (((17:ℝ)/133)+((1616381:ℝ)/171475)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have h1 : ((-2765365576647743:ℝ)/6859000000000000) ≤ (((-5:ℝ)/19)+((-17523723:ℝ)/342950)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have p1 := nonnegative_power_bounds y (1/22) hy0 hY 1
  have b1 := monomial_lower (((-5:ℝ)/19)+((-17523723:ℝ)/342950)*gamma 7) ((-2765365576647743:ℝ)/6859000000000000) (y^1) ((1/22)^1) h1 p1.1 p1.2
  norm_num at b1
  have h2 : ((-169179148467:ℝ)/4750000000000) ≤ (((0:ℝ)/1)+((-6174:ℝ)/475)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have p2 := nonnegative_power_bounds y (1/22) hy0 hY 2
  have b2 := monomial_lower (((0:ℝ)/1)+((-6174:ℝ)/475)*gamma 7) ((-169179148467:ℝ)/4750000000000) (y^2) ((1/22)^2) h2 p2.1 p2.2
  norm_num at b2
  have h3 : ((-48291248045747:ℝ)/19000000000000) ≤ (((0:ℝ)/1)+((-881167:ℝ)/950)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have p3 := nonnegative_power_bounds y (1/22) hy0 hY 3
  have b3 := monomial_lower (((0:ℝ)/1)+((-881167:ℝ)/950)*gamma 7) ((-48291248045747:ℝ)/19000000000000) (y^3) ((1/22)^3) h3 p3.1 p3.2
  norm_num at b3
  have he : poly (1/19) y = (((17:ℝ)/133)+((1616381:ℝ)/171475)*gamma 7)*y^0 + (((-5:ℝ)/19)+((-17523723:ℝ)/342950)*gamma 7)*y^1 + (((0:ℝ)/1)+((-6174:ℝ)/475)*gamma 7)*y^2 + (((0:ℝ)/1)+((-881167:ℝ)/950)*gamma 7)*y^3 := by
    unfold poly; generalize gamma 7 = g; norm_num; ring
  rw [he]
  generalize hG : gamma 7 = g at *
  generalize hL : log ((7:ℝ)/19) = ld at *
  norm_num at hx ⊢
  linarith only [ht, hx, h0, b1, b2, b3]

theorem mixed_20 (y : ℝ) (hy : 0 < y) (hY : y ≤ 1/22) :
    0 < poly (1/20) y+(1/20)*log (7/20)+y*log (7*y) := by
  have hy0 := hy.le
  have ht := tail_log y hy hY
  have hx := mul_le_mul_of_nonneg_left ratio_log_lower_20 (by norm_num : (0:ℝ) ≤ 1/20)
  have h0 : ((64592576051844973:ℝ)/420000000000000000) ≤ (((107:ℝ)/840)+((1927671:ℝ)/200000)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have h1 : ((-368124765316519:ℝ)/960000000000000) ≤ (((-29:ℝ)/120)+((-827953:ℝ)/16000)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have p1 := nonnegative_power_bounds y (1/22) hy0 hY 1
  have b1 := monomial_lower (((-29:ℝ)/120)+((-827953:ℝ)/16000)*gamma 7) ((-368124765316519:ℝ)/960000000000000) (y^1) ((1/22)^1) h1 p1.1 p1.2
  norm_num at b1
  have h2 : ((-56393049489:ℝ)/1000000000000) ≤ (((0:ℝ)/1)+((-1029:ℝ)/50)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have p2 := nonnegative_power_bounds y (1/22) hy0 hY 2
  have b2 := monomial_lower (((0:ℝ)/1)+((-1029:ℝ)/50)*gamma 7) ((-56393049489:ℝ)/1000000000000) (y^2) ((1/22)^2) h2 p2.1 p2.2
  norm_num at b2
  have h3 : ((-10131951224857:ℝ)/4000000000000) ≤ (((0:ℝ)/1)+((-184877:ℝ)/200)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have p3 := nonnegative_power_bounds y (1/22) hy0 hY 3
  have b3 := monomial_lower (((0:ℝ)/1)+((-184877:ℝ)/200)*gamma 7) ((-10131951224857:ℝ)/4000000000000) (y^3) ((1/22)^3) h3 p3.1 p3.2
  norm_num at b3
  have he : poly (1/20) y = (((107:ℝ)/840)+((1927671:ℝ)/200000)*gamma 7)*y^0 + (((-29:ℝ)/120)+((-827953:ℝ)/16000)*gamma 7)*y^1 + (((0:ℝ)/1)+((-1029:ℝ)/50)*gamma 7)*y^2 + (((0:ℝ)/1)+((-184877:ℝ)/200)*gamma 7)*y^3 := by
    unfold poly; generalize gamma 7 = g; norm_num; ring
  rw [he]
  generalize hG : gamma 7 = g at *
  generalize hL : log ((7:ℝ)/20) = ld at *
  norm_num at hx ⊢
  linarith only [ht, hx, h0, b1, b2, b3]

theorem mixed_21 (y : ℝ) (hy : 0 < y) (hY : y ≤ 1/22) :
    0 < poly (1/21) y+(1/21)*log (7/21)+y*log (7*y) := by
  have hy0 := hy.le
  have ht := tail_log y hy hY
  have hx := mul_le_mul_of_nonneg_left ratio_log_lower_21 (by norm_num : (0:ℝ) ≤ 1/21)
  have h0 : ((24240987466331:ℝ)/157500000000000) ≤ (((8:ℝ)/63)+((737:ℝ)/75)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have h1 : ((-9869637348269:ℝ)/27000000000000) ≤ (((-2:ℝ)/9)+((-70609:ℝ)/1350)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have p1 := nonnegative_power_bounds y (1/22) hy0 hY 1
  have b1 := monomial_lower (((-2:ℝ)/9)+((-70609:ℝ)/1350)*gamma 7) ((-9869637348269:ℝ)/27000000000000) (y^1) ((1/22)^1) h1 p1.1 p1.2
  norm_num at b1
  have h2 : ((-18797683163:ℝ)/250000000000) ≤ (((0:ℝ)/1)+((-686:ℝ)/25)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have p2 := nonnegative_power_bounds y (1/22) hy0 hY 2
  have b2 := monomial_lower (((0:ℝ)/1)+((-686:ℝ)/25)*gamma 7) ((-18797683163:ℝ)/250000000000) (y^2) ((1/22)^2) h2 p2.1 p2.2
  norm_num at b2
  have h3 : ((-7575466314689:ℝ)/3000000000000) ≤ (((0:ℝ)/1)+((-138229:ℝ)/150)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have p3 := nonnegative_power_bounds y (1/22) hy0 hY 3
  have b3 := monomial_lower (((0:ℝ)/1)+((-138229:ℝ)/150)*gamma 7) ((-7575466314689:ℝ)/3000000000000) (y^3) ((1/22)^3) h3 p3.1 p3.2
  norm_num at b3
  have he : poly (1/21) y = (((8:ℝ)/63)+((737:ℝ)/75)*gamma 7)*y^0 + (((-2:ℝ)/9)+((-70609:ℝ)/1350)*gamma 7)*y^1 + (((0:ℝ)/1)+((-686:ℝ)/25)*gamma 7)*y^2 + (((0:ℝ)/1)+((-138229:ℝ)/150)*gamma 7)*y^3 := by
    unfold poly; generalize gamma 7 = g; norm_num; ring
  rw [he]
  generalize hG : gamma 7 = g at *
  generalize hL : log ((7:ℝ)/21) = ld at *
  norm_num at hx ⊢
  linarith only [ht, hx, h0, b1, b2, b3]

theorem double_tail (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hX : x ≤ 1/22) (hY : y ≤ 1/22) :
    0 < poly x y+x*log (7*x)+y*log (7*y) := by
  have hxlog := tail_log x hx hX
  have hylog := tail_log y hy hY
  have h0 : ((-131583782141:ℝ)/40000000000) ≤ (((0:ℝ)/1)+((-2401:ℝ)/2)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have xp0 := nonnegative_power_bounds x (1/22) hx.le hX 3
  have yp0 := nonnegative_power_bounds y (1/22) hy.le hY 1
  have pp0 : x^3*y^1 ≤ (1/22)^3*(1/22)^1 := mul_le_mul xp0.2 yp0.2 yp0.1 (by norm_num)
  have b0 := monomial_lower (((0:ℝ)/1)+((-2401:ℝ)/2)*gamma 7) ((-131583782141:ℝ)/40000000000) (x^3*y^1) ((1/22)^3*(1/22)^1) h0 (mul_nonneg xp0.1 yp0.1) pp0
  norm_num at b0
  have h1 : ((-1184254039269:ℝ)/500000000000) ≤ (((0:ℝ)/1)+((-21609:ℝ)/25)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have xp1 := nonnegative_power_bounds x (1/22) hx.le hX 3
  have yp1 := nonnegative_power_bounds y (1/22) hy.le hY 0
  have pp1 : x^3*y^0 ≤ (1/22)^3*(1/22)^0 := mul_le_mul xp1.2 yp1.2 yp1.1 (by norm_num)
  have b1 := monomial_lower (((0:ℝ)/1)+((-21609:ℝ)/25)*gamma 7) ((-1184254039269:ℝ)/500000000000) (x^3*y^0) ((1/22)^3*(1/22)^0) h1 (mul_nonneg xp1.1 yp1.1) pp1
  norm_num at b1
  have h2 : ((1973756717709:ℝ)/250000000000) ≤ (((0:ℝ)/1)+((14406:ℝ)/5)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have xp2 := nonnegative_power_bounds x (1/22) hx.le hX 2
  have yp2 := nonnegative_power_bounds y (1/22) hy.le hY 1
  have pp2 : x^2*y^1 ≤ (1/22)^2*(1/22)^1 := mul_le_mul xp2.2 yp2.2 yp2.1 (by norm_num)
  have b2 := monomial_lower (((0:ℝ)/1)+((14406:ℝ)/5)*gamma 7) ((1973756717709:ℝ)/250000000000) (x^2*y^1) ((1/22)^2*(1/22)^1) h2 (mul_nonneg xp2.1 yp2.1) pp2
  norm_num at b2
  have h3 : ((-56393049489:ℝ)/125000000000) ≤ (((0:ℝ)/1)+((-4116:ℝ)/25)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have xp3 := nonnegative_power_bounds x (1/22) hx.le hX 2
  have yp3 := nonnegative_power_bounds y (1/22) hy.le hY 0
  have pp3 : x^2*y^0 ≤ (1/22)^2*(1/22)^0 := mul_le_mul xp3.2 yp3.2 yp3.1 (by norm_num)
  have b3 := monomial_lower (((0:ℝ)/1)+((-4116:ℝ)/25)*gamma 7) ((-56393049489:ℝ)/125000000000) (x^2*y^0) ((1/22)^2*(1/22)^0) h3 (mul_nonneg xp3.1 yp3.1) pp3
  norm_num at b3
  have h4 : ((-131583782141:ℝ)/40000000000) ≤ (((0:ℝ)/1)+((-2401:ℝ)/2)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have xp4 := nonnegative_power_bounds x (1/22) hx.le hX 1
  have yp4 := nonnegative_power_bounds y (1/22) hy.le hY 3
  have pp4 : x^1*y^3 ≤ (1/22)^1*(1/22)^3 := mul_le_mul xp4.2 yp4.2 yp4.1 (by norm_num)
  have b4 := monomial_lower (((0:ℝ)/1)+((-2401:ℝ)/2)*gamma 7) ((-131583782141:ℝ)/40000000000) (x^1*y^3) ((1/22)^1*(1/22)^3) h4 (mul_nonneg xp4.1 yp4.1) pp4
  norm_num at b4
  have h5 : ((1973756717709:ℝ)/250000000000) ≤ (((0:ℝ)/1)+((14406:ℝ)/5)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have xp5 := nonnegative_power_bounds x (1/22) hx.le hX 1
  have yp5 := nonnegative_power_bounds y (1/22) hy.le hY 2
  have pp5 : x^1*y^2 ≤ (1/22)^1*(1/22)^2 := mul_le_mul xp5.2 yp5.2 yp5.1 (by norm_num)
  have b5 := monomial_lower (((0:ℝ)/1)+((14406:ℝ)/5)*gamma 7) ((1973756717709:ℝ)/250000000000) (x^1*y^2) ((1/22)^1*(1/22)^2) h5 (mul_nonneg xp5.1 yp5.1) pp5
  norm_num at b5
  have h6 : ((-620556149927:ℝ)/75000000000) ≤ (((-49:ℝ)/6)+((-196:ℝ)/5)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have xp6 := nonnegative_power_bounds x (1/22) hx.le hX 1
  have yp6 := nonnegative_power_bounds y (1/22) hy.le hY 1
  have pp6 : x^1*y^1 ≤ (1/22)^1*(1/22)^1 := mul_le_mul xp6.2 yp6.2 yp6.1 (by norm_num)
  have b6 := monomial_lower (((-49:ℝ)/6)+((-196:ℝ)/5)*gamma 7) ((-620556149927:ℝ)/75000000000) (x^1*y^1) ((1/22)^1*(1/22)^1) h6 (mul_nonneg xp6.1 yp6.1) pp6
  norm_num at b6
  have h7 : ((16371652117:ℝ)/1500000000000) ≤ (((1:ℝ)/6)+((-1421:ℝ)/25)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have xp7 := nonnegative_power_bounds x (1/22) hx.le hX 1
  have yp7 := nonnegative_power_bounds y (1/22) hy.le hY 0
  have pp7 : x^1*y^0 ≤ (1/22)^1*(1/22)^0 := mul_le_mul xp7.2 yp7.2 yp7.1 (by norm_num)
  have b7 := monomial_lower (((1:ℝ)/6)+((-1421:ℝ)/25)*gamma 7) ((16371652117:ℝ)/1500000000000) (x^1*y^0) ((1/22)^1*(1/22)^0) h7 (mul_nonneg xp7.1 yp7.1) pp7
  norm_num at b7
  have h8 : ((-1184254039269:ℝ)/500000000000) ≤ (((0:ℝ)/1)+((-21609:ℝ)/25)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have xp8 := nonnegative_power_bounds x (1/22) hx.le hX 0
  have yp8 := nonnegative_power_bounds y (1/22) hy.le hY 3
  have pp8 : x^0*y^3 ≤ (1/22)^0*(1/22)^3 := mul_le_mul xp8.2 yp8.2 yp8.1 (by norm_num)
  have b8 := monomial_lower (((0:ℝ)/1)+((-21609:ℝ)/25)*gamma 7) ((-1184254039269:ℝ)/500000000000) (x^0*y^3) ((1/22)^0*(1/22)^3) h8 (mul_nonneg xp8.1 yp8.1) pp8
  norm_num at b8
  have h9 : ((-56393049489:ℝ)/125000000000) ≤ (((0:ℝ)/1)+((-4116:ℝ)/25)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have xp9 := nonnegative_power_bounds x (1/22) hx.le hX 0
  have yp9 := nonnegative_power_bounds y (1/22) hy.le hY 2
  have pp9 : x^0*y^2 ≤ (1/22)^0*(1/22)^2 := mul_le_mul xp9.2 yp9.2 yp9.1 (by norm_num)
  have b9 := monomial_lower (((0:ℝ)/1)+((-4116:ℝ)/25)*gamma 7) ((-56393049489:ℝ)/125000000000) (x^0*y^2) ((1/22)^0*(1/22)^2) h9 (mul_nonneg xp9.1 yp9.1) pp9
  norm_num at b9
  have h10 : ((16371652117:ℝ)/1500000000000) ≤ (((1:ℝ)/6)+((-1421:ℝ)/25)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  have xp10 := nonnegative_power_bounds x (1/22) hx.le hX 0
  have yp10 := nonnegative_power_bounds y (1/22) hy.le hY 1
  have pp10 : x^0*y^1 ≤ (1/22)^0*(1/22)^1 := mul_le_mul xp10.2 yp10.2 yp10.1 (by norm_num)
  have b10 := monomial_lower (((1:ℝ)/6)+((-1421:ℝ)/25)*gamma 7) ((16371652117:ℝ)/1500000000000) (x^0*y^1) ((1/22)^0*(1/22)^1) h10 (mul_nonneg xp10.1 yp10.1) pp10
  norm_num at b10
  have h11 : ((324807105919:ℝ)/2100000000000) ≤ (((5:ℝ)/42)+((13:ℝ)/1)*gamma 7) := by linarith [gamma_bounds.1, gamma_bounds.2]
  unfold poly
  generalize hG : gamma 7 = g at *
  norm_num
  linarith only [hxlog, hylog, h11, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10]


end SparseComponent.TotalFamily.Density7
