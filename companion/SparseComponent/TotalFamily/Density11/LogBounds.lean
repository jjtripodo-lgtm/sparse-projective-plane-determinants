import SparseComponent.TotalFamily.Density8.LogBounds
import SparseComponent.TotalFamily.PolynomialTools
import SparseComponent.TotalFamily.LogCertificates

namespace SparseComponent.TotalFamily.Density11
open Finset Matrix Real TotalOnes

set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

theorem log_two_precise : ((693147180559:ℝ)/1000000000000) ≤ log (2:ℝ) ∧ log (2:ℝ) ≤ ((8664339757:ℝ)/12500000000) := by
  exact Density8.log_two_precise

theorem log_12_11 : ((8701137:ℝ)/100000000) ≤ log ((12:ℝ)/11) ∧ log ((12:ℝ)/11) ≤ ((4350569:ℝ)/50000000) := by
  apply log_interval_of_atanh ((12:ℝ)/11) (by norm_num) 5
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_11_10 : ((9531017:ℝ)/100000000) ≤ log ((11:ℝ)/10) ∧ log ((11:ℝ)/10) ≤ ((4765509:ℝ)/50000000) := by
  apply log_interval_of_atanh ((11:ℝ)/10) (by norm_num) 6
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_13_11 : ((130511:ℝ)/781250) ≤ log ((13:ℝ)/11) ∧ log ((13:ℝ)/11) ≤ ((16705409:ℝ)/100000000) := by
  apply log_interval_of_atanh ((13:ℝ)/11) (by norm_num) 6
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_11_9 : ((20067069:ℝ)/100000000) ≤ log ((11:ℝ)/9) ∧ log ((11:ℝ)/9) ≤ ((2006707:ℝ)/10000000) := by
  apply log_interval_of_atanh ((11:ℝ)/9) (by norm_num) 6
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_14_11 : ((4823241:ℝ)/20000000) ≤ log ((14:ℝ)/11) ∧ log ((14:ℝ)/11) ≤ ((12058103:ℝ)/50000000) := by
  apply log_interval_of_atanh ((14:ℝ)/11) (by norm_num) 7
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_15_11 : ((7753873:ℝ)/25000000) ≤ log ((15:ℝ)/11) ∧ log ((15:ℝ)/11) ≤ ((31015493:ℝ)/100000000) := by
  apply log_interval_of_atanh ((15:ℝ)/11) (by norm_num) 8
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_11_8 : ((31845373:ℝ)/100000000) ≤ log ((11:ℝ)/8) ∧ log ((11:ℝ)/8) ≤ ((15922687:ℝ)/50000000) := by
  apply log_interval_of_atanh ((11:ℝ)/8) (by norm_num) 7
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_16_11 : ((1170917:ℝ)/3125000) ≤ log ((16:ℝ)/11) ∧ log ((16:ℝ)/11) ≤ ((7493869:ℝ)/20000000) := by
  apply log_interval_of_atanh ((16:ℝ)/11) (by norm_num) 9
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_17_11 : ((43531807:ℝ)/100000000) ≤ log ((17:ℝ)/11) ∧ log ((17:ℝ)/11) ≤ ((1360369:ℝ)/3125000) := by
  apply log_interval_of_atanh ((17:ℝ)/11) (by norm_num) 8
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_11_7 : ((2824907:ℝ)/6250000) ≤ log ((11:ℝ)/7) ∧ log ((11:ℝ)/7) ≤ ((45198513:ℝ)/100000000) := by
  apply log_interval_of_atanh ((11:ℝ)/7) (by norm_num) 9
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_18_11 : ((1538989:ℝ)/3125000) ≤ log ((18:ℝ)/11) ∧ log ((18:ℝ)/11) ≤ ((49247649:ℝ)/100000000) := by
  apply log_interval_of_atanh ((18:ℝ)/11) (by norm_num) 9
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_19_11 : ((5465437:ℝ)/10000000) ≤ log ((19:ℝ)/11) ∧ log ((19:ℝ)/11) ≤ ((54654371:ℝ)/100000000) := by
  apply log_interval_of_atanh ((19:ℝ)/11) (by norm_num) 10
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_20_11 : ((597837:ℝ)/1000000) ≤ log ((20:ℝ)/11) ∧ log ((20:ℝ)/11) ≤ ((59783701:ℝ)/100000000) := by
  apply log_interval_of_atanh ((20:ℝ)/11) (by norm_num) 10
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_11_6 : ((3030679:ℝ)/5000000) ≤ log ((11:ℝ)/6) ∧ log ((11:ℝ)/6) ≤ ((60613581:ℝ)/100000000) := by
  apply log_interval_of_atanh ((11:ℝ)/6) (by norm_num) 10
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_21_11 : ((16165679:ℝ)/25000000) ≤ log ((21:ℝ)/11) ∧ log ((21:ℝ)/11) ≤ ((64662717:ℝ)/100000000) := by
  apply log_interval_of_atanh ((21:ℝ)/11) (by norm_num) 11
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_2_1 : ((34657359:ℝ)/50000000) ≤ log ((2:ℝ)/1) ∧ log ((2:ℝ)/1) ≤ ((69314719:ℝ)/100000000) := by
  apply log_interval_of_atanh ((2:ℝ)/1) (by norm_num) 11
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_23_11 : ((36879947:ℝ)/50000000) ≤ log ((23:ℝ)/11) ∧ log ((23:ℝ)/11) ≤ ((14751979:ℝ)/20000000) := by
  apply log_interval_of_atanh ((23:ℝ)/11) (by norm_num) 11
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_24_11 : ((15603171:ℝ)/20000000) ≤ log ((24:ℝ)/11) ∧ log ((24:ℝ)/11) ≤ ((4875991:ℝ)/6250000) := by
  apply log_interval_of_atanh ((24:ℝ)/11) (by norm_num) 12
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_11_5 : ((9855717:ℝ)/12500000) ≤ log ((11:ℝ)/5) ∧ log ((11:ℝ)/5) ≤ ((78845737:ℝ)/100000000) := by
  apply log_interval_of_atanh ((11:ℝ)/5) (by norm_num) 12
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_25_11 : ((16419611:ℝ)/20000000) ≤ log ((25:ℝ)/11) ∧ log ((25:ℝ)/11) ≤ ((10262257:ℝ)/12500000) := by
  apply log_interval_of_atanh ((25:ℝ)/11) (by norm_num) 12
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_26_11 : ((43010063:ℝ)/50000000) ≤ log ((26:ℝ)/11) ∧ log ((26:ℝ)/11) ≤ ((86020127:ℝ)/100000000) := by
  apply log_interval_of_atanh ((26:ℝ)/11) (by norm_num) 13
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_27_11 : ((89794159:ℝ)/100000000) ≤ log ((27:ℝ)/11) ∧ log ((27:ℝ)/11) ≤ ((1122427:ℝ)/1250000) := by
  apply log_interval_of_atanh ((27:ℝ)/11) (by norm_num) 13
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_28_11 : ((93430923:ℝ)/100000000) ≤ log ((28:ℝ)/11) ∧ log ((28:ℝ)/11) ≤ ((23357731:ℝ)/25000000) := by
  apply log_interval_of_atanh ((28:ℝ)/11) (by norm_num) 14
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_29_11 : ((19388011:ℝ)/20000000) ≤ log ((29:ℝ)/11) ∧ log ((29:ℝ)/11) ≤ ((12117507:ℝ)/12500000) := by
  apply log_interval_of_atanh ((29:ℝ)/11) (by norm_num) 15
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_30_11 : ((10033021:ℝ)/10000000) ≤ log ((30:ℝ)/11) ∧ log ((30:ℝ)/11) ≤ ((100330211:ℝ)/100000000) := by
  apply log_interval_of_atanh ((30:ℝ)/11) (by norm_num) 16
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_11_4 : ((101160091:ℝ)/100000000) ≤ log ((11:ℝ)/4) ∧ log ((11:ℝ)/4) ≤ ((25290023:ℝ)/25000000) := by
  apply log_interval_of_atanh ((11:ℝ)/4) (by norm_num) 15
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_31_11 : ((103609193:ℝ)/100000000) ≤ log ((31:ℝ)/11) ∧ log ((31:ℝ)/11) ≤ ((51804597:ℝ)/50000000) := by
  apply log_interval_of_atanh ((31:ℝ)/11) (by norm_num) 15
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_32_11 : ((106784063:ℝ)/100000000) ≤ log ((32:ℝ)/11) ∧ log ((32:ℝ)/11) ≤ ((1668501:ℝ)/1562500) := by
  apply log_interval_of_atanh ((32:ℝ)/11) (by norm_num) 19
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_3_1 : ((27465307:ℝ)/25000000) ≤ log ((3:ℝ)/1) ∧ log ((3:ℝ)/1) ≤ ((109861229:ℝ)/100000000) := by
  apply log_interval_of_atanh ((3:ℝ)/1) (by norm_num) 17
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_34_11 : ((4513861:ℝ)/4000000) ≤ log ((34:ℝ)/11) ∧ log ((34:ℝ)/11) ≤ ((56423263:ℝ)/50000000) := by
  apply log_interval_of_atanh ((34:ℝ)/11) (by norm_num) 17
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_11_3 : ((64964149:ℝ)/50000000) ≤ log ((11:ℝ)/3) ∧ log ((11:ℝ)/3) ≤ ((129928299:ℝ)/100000000) := by
  apply log_interval_of_atanh ((11:ℝ)/3) (by norm_num) 20
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_10_1 : ((230258509:ℝ)/100000000) ≤ log ((10:ℝ)/1) ∧ log ((10:ℝ)/1) ≤ ((23025851:ℝ)/10000000) := by
  have hs : ((458145365937:ℝ)/500000000000) ≤ log ((5:ℝ)/2) ∧ log ((5:ℝ)/2) ≤ ((1466065171:ℝ)/1600000000) := by
    apply log_interval_of_atanh ((5:ℝ)/2) (by norm_num) 19
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have he : log ((10:ℝ)/1) = log ((5:ℝ)/2)+2*log (2:ℝ) := by
    rw [show ((10:ℝ)/1) = ((5:ℝ)/2)*(2:ℝ)^2 by norm_num, log_mul (by norm_num) (by norm_num), log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hs.1, hs.2, log_two_precise.1, log_two_precise.2]

theorem log_11_1 : ((239789527:ℝ)/100000000) ≤ log ((11:ℝ)/1) ∧ log ((11:ℝ)/1) ≤ ((29973691:ℝ)/12500000) := by
  have hs : ((505800455839:ℝ)/500000000000) ≤ log ((11:ℝ)/4) ∧ log ((11:ℝ)/4) ≤ ((1011600911679:ℝ)/1000000000000) := by
    apply log_interval_of_atanh ((11:ℝ)/4) (by norm_num) 21
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have he : log ((11:ℝ)/1) = log ((11:ℝ)/4)+2*log (2:ℝ) := by
    rw [show ((11:ℝ)/1) = ((11:ℝ)/4)*(2:ℝ)^2 by norm_num, log_mul (by norm_num) (by norm_num), log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hs.1, hs.2, log_two_precise.1, log_two_precise.2]

theorem log_121_10 : ((49864109:ℝ)/20000000) ≤ log ((121:ℝ)/10) ∧ log ((121:ℝ)/10) ≤ ((124660273:ℝ)/50000000) := by
  have hs : ((553455545741:ℝ)/500000000000) ≤ log ((121:ℝ)/40) ∧ log ((121:ℝ)/40) ≤ ((1106911091483:ℝ)/1000000000000) := by
    apply log_interval_of_atanh ((121:ℝ)/40) (by norm_num) 24
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have he : log ((121:ℝ)/10) = log ((121:ℝ)/40)+2*log (2:ℝ) := by
    rw [show ((121:ℝ)/10) = ((121:ℝ)/40)*(2:ℝ)^2 by norm_num, log_mul (by norm_num) (by norm_num), log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hs.1, hs.2, log_two_precise.1, log_two_precise.2]

theorem gamma_bounds : ((2794187:ℝ)/4000000000) ≤ gamma 11 ∧ gamma 11 ≤ ((17463669:ℝ)/25000000000) := by
  have h := log_121_10
  unfold gamma logGamma
  rw [← log_div (by norm_num : (11:ℝ)^2 ≠ 0) (by norm_num : (11:ℝ)-1 ≠ 0)]
  norm_num at h ⊢
  constructor <;> linarith

theorem ratio_log_lower_3 : ((64964149:ℝ)/50000000) ≤ log ((11:ℝ)/3) := by
  convert log_11_3.1 using 1 <;> norm_num

theorem ratio_log_lower_4 : ((101160091:ℝ)/100000000) ≤ log ((11:ℝ)/4) := by
  convert log_11_4.1 using 1 <;> norm_num

theorem ratio_log_lower_5 : ((9855717:ℝ)/12500000) ≤ log ((11:ℝ)/5) := by
  convert log_11_5.1 using 1 <;> norm_num

theorem ratio_log_lower_6 : ((3030679:ℝ)/5000000) ≤ log ((11:ℝ)/6) := by
  convert log_11_6.1 using 1 <;> norm_num

theorem ratio_log_lower_7 : ((2824907:ℝ)/6250000) ≤ log ((11:ℝ)/7) := by
  convert log_11_7.1 using 1 <;> norm_num

theorem ratio_log_lower_8 : ((31845373:ℝ)/100000000) ≤ log ((11:ℝ)/8) := by
  convert log_11_8.1 using 1 <;> norm_num

theorem ratio_log_lower_9 : ((20067069:ℝ)/100000000) ≤ log ((11:ℝ)/9) := by
  convert log_11_9.1 using 1 <;> norm_num

theorem ratio_log_lower_10 : ((9531017:ℝ)/100000000) ≤ log ((11:ℝ)/10) := by
  convert log_11_10.1 using 1 <;> norm_num

theorem ratio_log_lower_11 : ((0:ℝ)/1) ≤ log ((11:ℝ)/11) := by
  norm_num

theorem ratio_log_lower_12 : ((-4350569:ℝ)/50000000) ≤ log ((11:ℝ)/12) := by
  rw [show (11:ℝ)/12 = (((12:ℝ)/11))⁻¹ by norm_num, log_inv]
  linarith [log_12_11.2]

theorem ratio_log_lower_13 : ((-16705409:ℝ)/100000000) ≤ log ((11:ℝ)/13) := by
  rw [show (11:ℝ)/13 = (((13:ℝ)/11))⁻¹ by norm_num, log_inv]
  linarith [log_13_11.2]

theorem ratio_log_lower_14 : ((-12058103:ℝ)/50000000) ≤ log ((11:ℝ)/14) := by
  rw [show (11:ℝ)/14 = (((14:ℝ)/11))⁻¹ by norm_num, log_inv]
  linarith [log_14_11.2]

theorem ratio_log_lower_15 : ((-31015493:ℝ)/100000000) ≤ log ((11:ℝ)/15) := by
  rw [show (11:ℝ)/15 = (((15:ℝ)/11))⁻¹ by norm_num, log_inv]
  linarith [log_15_11.2]

theorem ratio_log_lower_16 : ((-7493869:ℝ)/20000000) ≤ log ((11:ℝ)/16) := by
  rw [show (11:ℝ)/16 = (((16:ℝ)/11))⁻¹ by norm_num, log_inv]
  linarith [log_16_11.2]

theorem ratio_log_lower_17 : ((-1360369:ℝ)/3125000) ≤ log ((11:ℝ)/17) := by
  rw [show (11:ℝ)/17 = (((17:ℝ)/11))⁻¹ by norm_num, log_inv]
  linarith [log_17_11.2]

theorem ratio_log_lower_18 : ((-49247649:ℝ)/100000000) ≤ log ((11:ℝ)/18) := by
  rw [show (11:ℝ)/18 = (((18:ℝ)/11))⁻¹ by norm_num, log_inv]
  linarith [log_18_11.2]

theorem ratio_log_lower_19 : ((-54654371:ℝ)/100000000) ≤ log ((11:ℝ)/19) := by
  rw [show (11:ℝ)/19 = (((19:ℝ)/11))⁻¹ by norm_num, log_inv]
  linarith [log_19_11.2]

theorem ratio_log_lower_20 : ((-59783701:ℝ)/100000000) ≤ log ((11:ℝ)/20) := by
  rw [show (11:ℝ)/20 = (((20:ℝ)/11))⁻¹ by norm_num, log_inv]
  linarith [log_20_11.2]

theorem ratio_log_lower_21 : ((-64662717:ℝ)/100000000) ≤ log ((11:ℝ)/21) := by
  rw [show (11:ℝ)/21 = (((21:ℝ)/11))⁻¹ by norm_num, log_inv]
  linarith [log_21_11.2]

theorem ratio_log_lower_22 : ((-69314719:ℝ)/100000000) ≤ log ((11:ℝ)/22) := by
  rw [show (11:ℝ)/22 = (((2:ℝ)/1))⁻¹ by norm_num, log_inv]
  linarith [log_2_1.2]

theorem ratio_log_lower_23 : ((-14751979:ℝ)/20000000) ≤ log ((11:ℝ)/23) := by
  rw [show (11:ℝ)/23 = (((23:ℝ)/11))⁻¹ by norm_num, log_inv]
  linarith [log_23_11.2]

theorem ratio_log_lower_24 : ((-4875991:ℝ)/6250000) ≤ log ((11:ℝ)/24) := by
  rw [show (11:ℝ)/24 = (((24:ℝ)/11))⁻¹ by norm_num, log_inv]
  linarith [log_24_11.2]

theorem ratio_log_lower_25 : ((-10262257:ℝ)/12500000) ≤ log ((11:ℝ)/25) := by
  rw [show (11:ℝ)/25 = (((25:ℝ)/11))⁻¹ by norm_num, log_inv]
  linarith [log_25_11.2]

theorem ratio_log_lower_26 : ((-86020127:ℝ)/100000000) ≤ log ((11:ℝ)/26) := by
  rw [show (11:ℝ)/26 = (((26:ℝ)/11))⁻¹ by norm_num, log_inv]
  linarith [log_26_11.2]

theorem ratio_log_lower_27 : ((-1122427:ℝ)/1250000) ≤ log ((11:ℝ)/27) := by
  rw [show (11:ℝ)/27 = (((27:ℝ)/11))⁻¹ by norm_num, log_inv]
  linarith [log_27_11.2]

theorem ratio_log_lower_28 : ((-23357731:ℝ)/25000000) ≤ log ((11:ℝ)/28) := by
  rw [show (11:ℝ)/28 = (((28:ℝ)/11))⁻¹ by norm_num, log_inv]
  linarith [log_28_11.2]

theorem ratio_log_lower_29 : ((-12117507:ℝ)/12500000) ≤ log ((11:ℝ)/29) := by
  rw [show (11:ℝ)/29 = (((29:ℝ)/11))⁻¹ by norm_num, log_inv]
  linarith [log_29_11.2]

theorem ratio_log_lower_30 : ((-100330211:ℝ)/100000000) ≤ log ((11:ℝ)/30) := by
  rw [show (11:ℝ)/30 = (((30:ℝ)/11))⁻¹ by norm_num, log_inv]
  linarith [log_30_11.2]

theorem ratio_log_lower_31 : ((-51804597:ℝ)/50000000) ≤ log ((11:ℝ)/31) := by
  rw [show (11:ℝ)/31 = (((31:ℝ)/11))⁻¹ by norm_num, log_inv]
  linarith [log_31_11.2]

theorem ratio_log_lower_32 : ((-1668501:ℝ)/1562500) ≤ log ((11:ℝ)/32) := by
  rw [show (11:ℝ)/32 = (((32:ℝ)/11))⁻¹ by norm_num, log_inv]
  linarith [log_32_11.2]

theorem ratio_log_lower_33 : ((-109861229:ℝ)/100000000) ≤ log ((11:ℝ)/33) := by
  rw [show (11:ℝ)/33 = (((3:ℝ)/1))⁻¹ by norm_num, log_inv]
  linarith [log_3_1.2]

theorem ratio_log_lower_34 : ((-56423263:ℝ)/50000000) ≤ log ((11:ℝ)/34) := by
  rw [show (11:ℝ)/34 = (((34:ℝ)/11))⁻¹ by norm_num, log_inv]
  linarith [log_34_11.2]

end SparseComponent.TotalFamily.Density11
