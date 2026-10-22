import SparseComponent.TotalFamily.Density8.LogBounds
import SparseComponent.TotalFamily.PolynomialTools
import SparseComponent.TotalFamily.LogCertificates

namespace SparseComponent.TotalFamily.Density9
open Finset Matrix Real TotalOnes

set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

theorem log_two_precise : ((693147180559:ℝ)/1000000000000) ≤ log (2:ℝ) ∧ log (2:ℝ) ≤ ((8664339757:ℝ)/12500000000) := by
  exact Density8.log_two_precise

theorem log_10_9 : ((10536051:ℝ)/100000000) ≤ log ((10:ℝ)/9) ∧ log ((10:ℝ)/9) ≤ ((2634013:ℝ)/25000000) := by
  apply log_interval_of_atanh ((10:ℝ)/9) (by norm_num) 5
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_9_8 : ((11778303:ℝ)/100000000) ≤ log ((9:ℝ)/8) ∧ log ((9:ℝ)/8) ≤ ((46009:ℝ)/390625) := by
  apply log_interval_of_atanh ((9:ℝ)/8) (by norm_num) 5
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_11_9 : ((20067069:ℝ)/100000000) ≤ log ((11:ℝ)/9) ∧ log ((11:ℝ)/9) ≤ ((2006707:ℝ)/10000000) := by
  apply log_interval_of_atanh ((11:ℝ)/9) (by norm_num) 6
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_9_7 : ((12565721:ℝ)/50000000) ≤ log ((9:ℝ)/7) ∧ log ((9:ℝ)/7) ≤ ((25131443:ℝ)/100000000) := by
  apply log_interval_of_atanh ((9:ℝ)/7) (by norm_num) 7
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_4_3 : ((28768207:ℝ)/100000000) ≤ log ((4:ℝ)/3) ∧ log ((4:ℝ)/3) ≤ ((1798013:ℝ)/6250000) := by
  apply log_interval_of_atanh ((4:ℝ)/3) (by norm_num) 7
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_13_9 : ((18386239:ℝ)/50000000) ≤ log ((13:ℝ)/9) ∧ log ((13:ℝ)/9) ≤ ((36772479:ℝ)/100000000) := by
  apply log_interval_of_atanh ((13:ℝ)/9) (by norm_num) 8
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_3_2 : ((4054651:ℝ)/10000000) ≤ log ((3:ℝ)/2) ∧ log ((3:ℝ)/2) ≤ ((40546511:ℝ)/100000000) := by
  apply log_interval_of_atanh ((3:ℝ)/2) (by norm_num) 8
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_14_9 : ((1767331:ℝ)/4000000) ≤ log ((14:ℝ)/9) ∧ log ((14:ℝ)/9) ≤ ((11045819:ℝ)/25000000) := by
  apply log_interval_of_atanh ((14:ℝ)/9) (by norm_num) 8
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_5_3 : ((25541281:ℝ)/50000000) ≤ log ((5:ℝ)/3) ∧ log ((5:ℝ)/3) ≤ ((51082563:ℝ)/100000000) := by
  apply log_interval_of_atanh ((5:ℝ)/3) (by norm_num) 9
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_16_9 : ((28768207:ℝ)/50000000) ≤ log ((16:ℝ)/9) ∧ log ((16:ℝ)/9) ≤ ((11507283:ℝ)/20000000) := by
  apply log_interval_of_atanh ((16:ℝ)/9) (by norm_num) 10
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_9_5 : ((29389333:ℝ)/50000000) ≤ log ((9:ℝ)/5) ∧ log ((9:ℝ)/5) ≤ ((58778667:ℝ)/100000000) := by
  apply log_interval_of_atanh ((9:ℝ)/5) (by norm_num) 10
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_17_9 : ((15899719:ℝ)/25000000) ≤ log ((17:ℝ)/9) ∧ log ((17:ℝ)/9) ≤ ((63598877:ℝ)/100000000) := by
  apply log_interval_of_atanh ((17:ℝ)/9) (by norm_num) 11
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_2_1 : ((34657359:ℝ)/50000000) ≤ log ((2:ℝ)/1) ∧ log ((2:ℝ)/1) ≤ ((69314719:ℝ)/100000000) := by
  apply log_interval_of_atanh ((2:ℝ)/1) (by norm_num) 11
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_19_9 : ((467009:ℝ)/625000) ≤ log ((19:ℝ)/9) ∧ log ((19:ℝ)/9) ≤ ((74721441:ℝ)/100000000) := by
  apply log_interval_of_atanh ((19:ℝ)/9) (by norm_num) 11
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_20_9 : ((79850769:ℝ)/100000000) ≤ log ((20:ℝ)/9) ∧ log ((20:ℝ)/9) ≤ ((7985077:ℝ)/10000000) := by
  apply log_interval_of_atanh ((20:ℝ)/9) (by norm_num) 12
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_9_4 : ((81093021:ℝ)/100000000) ≤ log ((9:ℝ)/4) ∧ log ((9:ℝ)/4) ≤ ((40546511:ℝ)/50000000) := by
  apply log_interval_of_atanh ((9:ℝ)/4) (by norm_num) 13
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_7_3 : ((42364893:ℝ)/50000000) ≤ log ((7:ℝ)/3) ∧ log ((7:ℝ)/3) ≤ ((84729787:ℝ)/100000000) := by
  apply log_interval_of_atanh ((7:ℝ)/3) (by norm_num) 13
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_22_9 : ((89381787:ℝ)/100000000) ≤ log ((22:ℝ)/9) ∧ log ((22:ℝ)/9) ≤ ((22345447:ℝ)/25000000) := by
  apply log_interval_of_atanh ((22:ℝ)/9) (by norm_num) 14
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_23_9 : ((93826963:ℝ)/100000000) ≤ log ((23:ℝ)/9) ∧ log ((23:ℝ)/9) ≤ ((23456741:ℝ)/25000000) := by
  apply log_interval_of_atanh ((23:ℝ)/9) (by norm_num) 15
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_8_3 : ((3923317:ℝ)/4000000) ≤ log ((8:ℝ)/3) ∧ log ((8:ℝ)/3) ≤ ((49041463:ℝ)/50000000) := by
  apply log_interval_of_atanh ((8:ℝ)/3) (by norm_num) 14
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_25_9 : ((25541281:ℝ)/25000000) ≤ log ((25:ℝ)/9) ∧ log ((25:ℝ)/9) ≤ ((817321:ℝ)/800000) := by
  apply log_interval_of_atanh ((25:ℝ)/9) (by norm_num) 16
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_26_9 : ((26521799:ℝ)/25000000) ≤ log ((26:ℝ)/9) ∧ log ((26:ℝ)/9) ≤ ((106087197:ℝ)/100000000) := by
  apply log_interval_of_atanh ((26:ℝ)/9) (by norm_num) 15
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_3_1 : ((27465307:ℝ)/25000000) ≤ log ((3:ℝ)/1) ∧ log ((3:ℝ)/1) ≤ ((109861229:ℝ)/100000000) := by
  apply log_interval_of_atanh ((3:ℝ)/1) (by norm_num) 17
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_28_9 : ((113497993:ℝ)/100000000) ≤ log ((28:ℝ)/9) ∧ log ((28:ℝ)/9) ≤ ((56748997:ℝ)/50000000) := by
  apply log_interval_of_atanh ((28:ℝ)/9) (by norm_num) 17
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_9_2 : ((150407739:ℝ)/100000000) ≤ log ((9:ℝ)/2) ∧ log ((9:ℝ)/2) ≤ ((7520387:ℝ)/5000000) := by
  have hs : ((14722879457:ℝ)/125000000000) ≤ log ((9:ℝ)/8) ∧ log ((9:ℝ)/8) ≤ ((117783035657:ℝ)/1000000000000) := by
    apply log_interval_of_atanh ((9:ℝ)/8) (by norm_num) 7
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have he : log ((9:ℝ)/2) = log ((9:ℝ)/8)+2*log (2:ℝ) := by
    rw [show ((9:ℝ)/2) = ((9:ℝ)/8)*(2:ℝ)^2 by norm_num, log_mul (by norm_num) (by norm_num), log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hs.1, hs.2, log_two_precise.1, log_two_precise.2]

theorem log_8_1 : ((103972077:ℝ)/50000000) ≤ log ((8:ℝ)/1) ∧ log ((8:ℝ)/1) ≤ ((41588831:ℝ)/20000000) := by
  have hs : ((693147180559:ℝ)/1000000000000) ≤ log ((2:ℝ)/1) ∧ log ((2:ℝ)/1) ≤ ((8664339757:ℝ)/12500000000) := by
    simpa only [div_one] using log_two_precise
  have he : log ((8:ℝ)/1) = log ((2:ℝ)/1)+2*log (2:ℝ) := by
    rw [show ((8:ℝ)/1) = ((2:ℝ)/1)*(2:ℝ)^2 by norm_num, log_mul (by norm_num) (by norm_num), log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hs.1, hs.2, log_two_precise.1, log_two_precise.2]

theorem log_9_1 : ((219722457:ℝ)/100000000) ≤ log ((9:ℝ)/1) ∧ log ((9:ℝ)/1) ≤ ((109861229:ℝ)/50000000) := by
  have hs : ((101366277027:ℝ)/125000000000) ≤ log ((9:ℝ)/4) ∧ log ((9:ℝ)/4) ≤ ((810930216217:ℝ)/1000000000000) := by
    apply log_interval_of_atanh ((9:ℝ)/4) (by norm_num) 17
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have he : log ((9:ℝ)/1) = log ((9:ℝ)/4)+2*log (2:ℝ) := by
    rw [show ((9:ℝ)/1) = ((9:ℝ)/4)*(2:ℝ)^2 by norm_num, log_mul (by norm_num) (by norm_num), log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hs.1, hs.2, log_two_precise.1, log_two_precise.2]

theorem log_81_8 : ((231500761:ℝ)/100000000) ≤ log ((81:ℝ)/8) ∧ log ((81:ℝ)/8) ≤ ((115750381:ℝ)/50000000) := by
  have hs : ((29022289121:ℝ)/31250000000) ≤ log ((81:ℝ)/32) ∧ log ((81:ℝ)/32) ≤ ((928713251873:ℝ)/1000000000000) := by
    apply log_interval_of_atanh ((81:ℝ)/32) (by norm_num) 20
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have he : log ((81:ℝ)/8) = log ((81:ℝ)/32)+2*log (2:ℝ) := by
    rw [show ((81:ℝ)/8) = ((81:ℝ)/32)*(2:ℝ)^2 by norm_num, log_mul (by norm_num) (by norm_num), log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hs.1, hs.2, log_two_precise.1, log_two_precise.2]

theorem gamma_bounds : ((127791187:ℝ)/100000000000) ≤ gamma 9 ∧ gamma 9 ≤ ((31947797:ℝ)/25000000000) := by
  have h := log_81_8
  unfold gamma logGamma
  rw [← log_div (by norm_num : (9:ℝ)^2 ≠ 0) (by norm_num : (9:ℝ)-1 ≠ 0)]
  norm_num at h ⊢
  constructor <;> linarith

theorem ratio_log_lower_2 : ((150407739:ℝ)/100000000) ≤ log ((9:ℝ)/2) := by
  convert log_9_2.1 using 1 <;> norm_num

theorem ratio_log_lower_3 : ((27465307:ℝ)/25000000) ≤ log ((9:ℝ)/3) := by
  convert log_3_1.1 using 1 <;> norm_num

theorem ratio_log_lower_4 : ((81093021:ℝ)/100000000) ≤ log ((9:ℝ)/4) := by
  convert log_9_4.1 using 1 <;> norm_num

theorem ratio_log_lower_5 : ((29389333:ℝ)/50000000) ≤ log ((9:ℝ)/5) := by
  convert log_9_5.1 using 1 <;> norm_num

theorem ratio_log_lower_6 : ((4054651:ℝ)/10000000) ≤ log ((9:ℝ)/6) := by
  convert log_3_2.1 using 1 <;> norm_num

theorem ratio_log_lower_7 : ((12565721:ℝ)/50000000) ≤ log ((9:ℝ)/7) := by
  convert log_9_7.1 using 1 <;> norm_num

theorem ratio_log_lower_8 : ((11778303:ℝ)/100000000) ≤ log ((9:ℝ)/8) := by
  convert log_9_8.1 using 1 <;> norm_num

theorem ratio_log_lower_9 : ((0:ℝ)/1) ≤ log ((9:ℝ)/9) := by
  norm_num

theorem ratio_log_lower_10 : ((-2634013:ℝ)/25000000) ≤ log ((9:ℝ)/10) := by
  rw [show (9:ℝ)/10 = (((10:ℝ)/9))⁻¹ by norm_num, log_inv]
  linarith [log_10_9.2]

theorem ratio_log_lower_11 : ((-2006707:ℝ)/10000000) ≤ log ((9:ℝ)/11) := by
  rw [show (9:ℝ)/11 = (((11:ℝ)/9))⁻¹ by norm_num, log_inv]
  linarith [log_11_9.2]

theorem ratio_log_lower_12 : ((-1798013:ℝ)/6250000) ≤ log ((9:ℝ)/12) := by
  rw [show (9:ℝ)/12 = (((4:ℝ)/3))⁻¹ by norm_num, log_inv]
  linarith [log_4_3.2]

theorem ratio_log_lower_13 : ((-36772479:ℝ)/100000000) ≤ log ((9:ℝ)/13) := by
  rw [show (9:ℝ)/13 = (((13:ℝ)/9))⁻¹ by norm_num, log_inv]
  linarith [log_13_9.2]

theorem ratio_log_lower_14 : ((-11045819:ℝ)/25000000) ≤ log ((9:ℝ)/14) := by
  rw [show (9:ℝ)/14 = (((14:ℝ)/9))⁻¹ by norm_num, log_inv]
  linarith [log_14_9.2]

theorem ratio_log_lower_15 : ((-51082563:ℝ)/100000000) ≤ log ((9:ℝ)/15) := by
  rw [show (9:ℝ)/15 = (((5:ℝ)/3))⁻¹ by norm_num, log_inv]
  linarith [log_5_3.2]

theorem ratio_log_lower_16 : ((-11507283:ℝ)/20000000) ≤ log ((9:ℝ)/16) := by
  rw [show (9:ℝ)/16 = (((16:ℝ)/9))⁻¹ by norm_num, log_inv]
  linarith [log_16_9.2]

theorem ratio_log_lower_17 : ((-63598877:ℝ)/100000000) ≤ log ((9:ℝ)/17) := by
  rw [show (9:ℝ)/17 = (((17:ℝ)/9))⁻¹ by norm_num, log_inv]
  linarith [log_17_9.2]

theorem ratio_log_lower_18 : ((-69314719:ℝ)/100000000) ≤ log ((9:ℝ)/18) := by
  rw [show (9:ℝ)/18 = (((2:ℝ)/1))⁻¹ by norm_num, log_inv]
  linarith [log_2_1.2]

theorem ratio_log_lower_19 : ((-74721441:ℝ)/100000000) ≤ log ((9:ℝ)/19) := by
  rw [show (9:ℝ)/19 = (((19:ℝ)/9))⁻¹ by norm_num, log_inv]
  linarith [log_19_9.2]

theorem ratio_log_lower_20 : ((-7985077:ℝ)/10000000) ≤ log ((9:ℝ)/20) := by
  rw [show (9:ℝ)/20 = (((20:ℝ)/9))⁻¹ by norm_num, log_inv]
  linarith [log_20_9.2]

theorem ratio_log_lower_21 : ((-84729787:ℝ)/100000000) ≤ log ((9:ℝ)/21) := by
  rw [show (9:ℝ)/21 = (((7:ℝ)/3))⁻¹ by norm_num, log_inv]
  linarith [log_7_3.2]

theorem ratio_log_lower_22 : ((-22345447:ℝ)/25000000) ≤ log ((9:ℝ)/22) := by
  rw [show (9:ℝ)/22 = (((22:ℝ)/9))⁻¹ by norm_num, log_inv]
  linarith [log_22_9.2]

theorem ratio_log_lower_23 : ((-23456741:ℝ)/25000000) ≤ log ((9:ℝ)/23) := by
  rw [show (9:ℝ)/23 = (((23:ℝ)/9))⁻¹ by norm_num, log_inv]
  linarith [log_23_9.2]

theorem ratio_log_lower_24 : ((-49041463:ℝ)/50000000) ≤ log ((9:ℝ)/24) := by
  rw [show (9:ℝ)/24 = (((8:ℝ)/3))⁻¹ by norm_num, log_inv]
  linarith [log_8_3.2]

theorem ratio_log_lower_25 : ((-817321:ℝ)/800000) ≤ log ((9:ℝ)/25) := by
  rw [show (9:ℝ)/25 = (((25:ℝ)/9))⁻¹ by norm_num, log_inv]
  linarith [log_25_9.2]

theorem ratio_log_lower_26 : ((-106087197:ℝ)/100000000) ≤ log ((9:ℝ)/26) := by
  rw [show (9:ℝ)/26 = (((26:ℝ)/9))⁻¹ by norm_num, log_inv]
  linarith [log_26_9.2]

theorem ratio_log_lower_27 : ((-109861229:ℝ)/100000000) ≤ log ((9:ℝ)/27) := by
  rw [show (9:ℝ)/27 = (((3:ℝ)/1))⁻¹ by norm_num, log_inv]
  linarith [log_3_1.2]

theorem ratio_log_lower_28 : ((-56748997:ℝ)/50000000) ≤ log ((9:ℝ)/28) := by
  rw [show (9:ℝ)/28 = (((28:ℝ)/9))⁻¹ by norm_num, log_inv]
  linarith [log_28_9.2]

end SparseComponent.TotalFamily.Density9
