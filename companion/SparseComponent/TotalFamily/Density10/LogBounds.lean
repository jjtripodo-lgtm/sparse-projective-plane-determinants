import SparseComponent.TotalFamily.Density8.LogBounds
import SparseComponent.TotalFamily.PolynomialTools
import SparseComponent.TotalFamily.LogCertificates

namespace SparseComponent.TotalFamily.Density10
open Finset Matrix Real TotalOnes

set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

theorem log_two_precise : ((693147180559:ℝ)/1000000000000) ≤ log (2:ℝ) ∧ log (2:ℝ) ≤ ((8664339757:ℝ)/12500000000) := by
  exact Density8.log_two_precise

theorem log_11_10 : ((9531017:ℝ)/100000000) ≤ log ((11:ℝ)/10) ∧ log ((11:ℝ)/10) ≤ ((4765509:ℝ)/50000000) := by
  apply log_interval_of_atanh ((11:ℝ)/10) (by norm_num) 6
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_10_9 : ((10536051:ℝ)/100000000) ≤ log ((10:ℝ)/9) ∧ log ((10:ℝ)/9) ≤ ((2634013:ℝ)/25000000) := by
  apply log_interval_of_atanh ((10:ℝ)/9) (by norm_num) 5
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_6_5 : ((3646431:ℝ)/20000000) ≤ log ((6:ℝ)/5) ∧ log ((6:ℝ)/5) ≤ ((4558039:ℝ)/25000000) := by
  apply log_interval_of_atanh ((6:ℝ)/5) (by norm_num) 6
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_5_4 : ((4462871:ℝ)/20000000) ≤ log ((5:ℝ)/4) ∧ log ((5:ℝ)/4) ≤ ((5578589:ℝ)/25000000) := by
  apply log_interval_of_atanh ((5:ℝ)/4) (by norm_num) 6
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_13_10 : ((13118213:ℝ)/50000000) ≤ log ((13:ℝ)/10) ∧ log ((13:ℝ)/10) ≤ ((26236427:ℝ)/100000000) := by
  apply log_interval_of_atanh ((13:ℝ)/10) (by norm_num) 7
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_7_5 : ((33647223:ℝ)/100000000) ≤ log ((7:ℝ)/5) ∧ log ((7:ℝ)/5) ≤ ((4205903:ℝ)/12500000) := by
  apply log_interval_of_atanh ((7:ℝ)/5) (by norm_num) 8
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_10_7 : ((17833747:ℝ)/50000000) ≤ log ((10:ℝ)/7) ∧ log ((10:ℝ)/7) ≤ ((7133499:ℝ)/20000000) := by
  apply log_interval_of_atanh ((10:ℝ)/7) (by norm_num) 8
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_3_2 : ((4054651:ℝ)/10000000) ≤ log ((3:ℝ)/2) ∧ log ((3:ℝ)/2) ≤ ((40546511:ℝ)/100000000) := by
  apply log_interval_of_atanh ((3:ℝ)/2) (by norm_num) 8
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_8_5 : ((23500181:ℝ)/50000000) ≤ log ((8:ℝ)/5) ∧ log ((8:ℝ)/5) ≤ ((47000363:ℝ)/100000000) := by
  apply log_interval_of_atanh ((8:ℝ)/5) (by norm_num) 9
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_5_3 : ((25541281:ℝ)/50000000) ≤ log ((5:ℝ)/3) ∧ log ((5:ℝ)/3) ≤ ((51082563:ℝ)/100000000) := by
  apply log_interval_of_atanh ((5:ℝ)/3) (by norm_num) 9
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_17_10 : ((2122513:ℝ)/4000000) ≤ log ((17:ℝ)/10) ∧ log ((17:ℝ)/10) ≤ ((26531413:ℝ)/50000000) := by
  apply log_interval_of_atanh ((17:ℝ)/10) (by norm_num) 9
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_9_5 : ((29389333:ℝ)/50000000) ≤ log ((9:ℝ)/5) ∧ log ((9:ℝ)/5) ≤ ((58778667:ℝ)/100000000) := by
  apply log_interval_of_atanh ((9:ℝ)/5) (by norm_num) 10
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_19_10 : ((16046347:ℝ)/25000000) ≤ log ((19:ℝ)/10) ∧ log ((19:ℝ)/10) ≤ ((64185389:ℝ)/100000000) := by
  apply log_interval_of_atanh ((19:ℝ)/10) (by norm_num) 11
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_2_1 : ((34657359:ℝ)/50000000) ≤ log ((2:ℝ)/1) ∧ log ((2:ℝ)/1) ≤ ((69314719:ℝ)/100000000) := by
  apply log_interval_of_atanh ((2:ℝ)/1) (by norm_num) 11
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_21_10 : ((37096867:ℝ)/50000000) ≤ log ((21:ℝ)/10) ∧ log ((21:ℝ)/10) ≤ ((14838747:ℝ)/20000000) := by
  apply log_interval_of_atanh ((21:ℝ)/10) (by norm_num) 12
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_11_5 : ((9855717:ℝ)/12500000) ≤ log ((11:ℝ)/5) ∧ log ((11:ℝ)/5) ≤ ((78845737:ℝ)/100000000) := by
  apply log_interval_of_atanh ((11:ℝ)/5) (by norm_num) 12
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_23_10 : ((2602841:ℝ)/3125000) ≤ log ((23:ℝ)/10) ∧ log ((23:ℝ)/10) ≤ ((83290913:ℝ)/100000000) := by
  apply log_interval_of_atanh ((23:ℝ)/10) (by norm_num) 13
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_12_5 : ((87546873:ℝ)/100000000) ≤ log ((12:ℝ)/5) ∧ log ((12:ℝ)/5) ≤ ((43773437:ℝ)/50000000) := by
  apply log_interval_of_atanh ((12:ℝ)/5) (by norm_num) 14
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_5_2 : ((91629073:ℝ)/100000000) ≤ log ((5:ℝ)/2) ∧ log ((5:ℝ)/2) ≤ ((45814537:ℝ)/50000000) := by
  apply log_interval_of_atanh ((5:ℝ)/2) (by norm_num) 13
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_13_5 : ((11943893:ℝ)/12500000) ≤ log ((13:ℝ)/5) ∧ log ((13:ℝ)/5) ≤ ((19110229:ℝ)/20000000) := by
  apply log_interval_of_atanh ((13:ℝ)/5) (by norm_num) 14
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_27_10 : ((99325177:ℝ)/100000000) ≤ log ((27:ℝ)/10) ∧ log ((27:ℝ)/10) ≤ ((49662589:ℝ)/50000000) := by
  apply log_interval_of_atanh ((27:ℝ)/10) (by norm_num) 15
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_14_5 : ((102961941:ℝ)/100000000) ≤ log ((14:ℝ)/5) ∧ log ((14:ℝ)/5) ≤ ((51480971:ℝ)/50000000) := by
  apply log_interval_of_atanh ((14:ℝ)/5) (by norm_num) 16
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_29_10 : ((106471073:ℝ)/100000000) ≤ log ((29:ℝ)/10) ∧ log ((29:ℝ)/10) ≤ ((53235537:ℝ)/50000000) := by
  apply log_interval_of_atanh ((29:ℝ)/10) (by norm_num) 16
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_3_1 : ((27465307:ℝ)/25000000) ≤ log ((3:ℝ)/1) ∧ log ((3:ℝ)/1) ≤ ((109861229:ℝ)/100000000) := by
  apply log_interval_of_atanh ((3:ℝ)/1) (by norm_num) 17
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_31_10 : ((113140211:ℝ)/100000000) ≤ log ((31:ℝ)/10) ∧ log ((31:ℝ)/10) ≤ ((28285053:ℝ)/25000000) := by
  apply log_interval_of_atanh ((31:ℝ)/10) (by norm_num) 17
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_10_3 : ((752483:ℝ)/625000) ≤ log ((10:ℝ)/3) ∧ log ((10:ℝ)/3) ≤ ((120397281:ℝ)/100000000) := by
  apply log_interval_of_atanh ((10:ℝ)/3) (by norm_num) 18
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_5_1 : ((160943791:ℝ)/100000000) ≤ log ((5:ℝ)/1) ∧ log ((5:ℝ)/1) ≤ ((10058987:ℝ)/6250000) := by
  have hs : ((111571775657:ℝ)/500000000000) ≤ log ((5:ℝ)/4) ∧ log ((5:ℝ)/4) ≤ ((44628710263:ℝ)/200000000000) := by
    apply log_interval_of_atanh ((5:ℝ)/4) (by norm_num) 8
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have he : log ((5:ℝ)/1) = log ((5:ℝ)/4)+2*log (2:ℝ) := by
    rw [show ((5:ℝ)/1) = ((5:ℝ)/4)*(2:ℝ)^2 by norm_num, log_mul (by norm_num) (by norm_num), log_pow]
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

theorem log_100_9 : ((752483:ℝ)/312500) ≤ log ((100:ℝ)/9) ∧ log ((100:ℝ)/9) ≤ ((240794561:ℝ)/100000000) := by
  have hs : ((1021651247531:ℝ)/1000000000000) ≤ log ((25:ℝ)/9) ∧ log ((25:ℝ)/9) ≤ ((255412811883:ℝ)/250000000000) := by
    apply log_interval_of_atanh ((25:ℝ)/9) (by norm_num) 24
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have he : log ((100:ℝ)/9) = log ((25:ℝ)/9)+2*log (2:ℝ) := by
    rw [show ((100:ℝ)/9) = ((25:ℝ)/9)*(2:ℝ)^2 by norm_num, log_mul (by norm_num) (by norm_num), log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hs.1, hs.2, log_two_precise.1, log_two_precise.2]

theorem gamma_bounds : ((18604433:ℝ)/20000000000) ≤ gamma 10 ∧ gamma 10 ≤ ((46511083:ℝ)/50000000000) := by
  have h := log_100_9
  unfold gamma logGamma
  rw [← log_div (by norm_num : (10:ℝ)^2 ≠ 0) (by norm_num : (10:ℝ)-1 ≠ 0)]
  norm_num at h ⊢
  constructor <;> linarith

theorem ratio_log_lower_2 : ((160943791:ℝ)/100000000) ≤ log ((10:ℝ)/2) := by
  convert log_5_1.1 using 1 <;> norm_num

theorem ratio_log_lower_3 : ((752483:ℝ)/625000) ≤ log ((10:ℝ)/3) := by
  convert log_10_3.1 using 1 <;> norm_num

theorem ratio_log_lower_4 : ((91629073:ℝ)/100000000) ≤ log ((10:ℝ)/4) := by
  convert log_5_2.1 using 1 <;> norm_num

theorem ratio_log_lower_5 : ((34657359:ℝ)/50000000) ≤ log ((10:ℝ)/5) := by
  convert log_2_1.1 using 1 <;> norm_num

theorem ratio_log_lower_6 : ((25541281:ℝ)/50000000) ≤ log ((10:ℝ)/6) := by
  convert log_5_3.1 using 1 <;> norm_num

theorem ratio_log_lower_7 : ((17833747:ℝ)/50000000) ≤ log ((10:ℝ)/7) := by
  convert log_10_7.1 using 1 <;> norm_num

theorem ratio_log_lower_8 : ((4462871:ℝ)/20000000) ≤ log ((10:ℝ)/8) := by
  convert log_5_4.1 using 1 <;> norm_num

theorem ratio_log_lower_9 : ((10536051:ℝ)/100000000) ≤ log ((10:ℝ)/9) := by
  convert log_10_9.1 using 1 <;> norm_num

theorem ratio_log_lower_10 : ((0:ℝ)/1) ≤ log ((10:ℝ)/10) := by
  norm_num

theorem ratio_log_lower_11 : ((-4765509:ℝ)/50000000) ≤ log ((10:ℝ)/11) := by
  rw [show (10:ℝ)/11 = (((11:ℝ)/10))⁻¹ by norm_num, log_inv]
  linarith [log_11_10.2]

theorem ratio_log_lower_12 : ((-4558039:ℝ)/25000000) ≤ log ((10:ℝ)/12) := by
  rw [show (10:ℝ)/12 = (((6:ℝ)/5))⁻¹ by norm_num, log_inv]
  linarith [log_6_5.2]

theorem ratio_log_lower_13 : ((-26236427:ℝ)/100000000) ≤ log ((10:ℝ)/13) := by
  rw [show (10:ℝ)/13 = (((13:ℝ)/10))⁻¹ by norm_num, log_inv]
  linarith [log_13_10.2]

theorem ratio_log_lower_14 : ((-4205903:ℝ)/12500000) ≤ log ((10:ℝ)/14) := by
  rw [show (10:ℝ)/14 = (((7:ℝ)/5))⁻¹ by norm_num, log_inv]
  linarith [log_7_5.2]

theorem ratio_log_lower_15 : ((-40546511:ℝ)/100000000) ≤ log ((10:ℝ)/15) := by
  rw [show (10:ℝ)/15 = (((3:ℝ)/2))⁻¹ by norm_num, log_inv]
  linarith [log_3_2.2]

theorem ratio_log_lower_16 : ((-47000363:ℝ)/100000000) ≤ log ((10:ℝ)/16) := by
  rw [show (10:ℝ)/16 = (((8:ℝ)/5))⁻¹ by norm_num, log_inv]
  linarith [log_8_5.2]

theorem ratio_log_lower_17 : ((-26531413:ℝ)/50000000) ≤ log ((10:ℝ)/17) := by
  rw [show (10:ℝ)/17 = (((17:ℝ)/10))⁻¹ by norm_num, log_inv]
  linarith [log_17_10.2]

theorem ratio_log_lower_18 : ((-58778667:ℝ)/100000000) ≤ log ((10:ℝ)/18) := by
  rw [show (10:ℝ)/18 = (((9:ℝ)/5))⁻¹ by norm_num, log_inv]
  linarith [log_9_5.2]

theorem ratio_log_lower_19 : ((-64185389:ℝ)/100000000) ≤ log ((10:ℝ)/19) := by
  rw [show (10:ℝ)/19 = (((19:ℝ)/10))⁻¹ by norm_num, log_inv]
  linarith [log_19_10.2]

theorem ratio_log_lower_20 : ((-69314719:ℝ)/100000000) ≤ log ((10:ℝ)/20) := by
  rw [show (10:ℝ)/20 = (((2:ℝ)/1))⁻¹ by norm_num, log_inv]
  linarith [log_2_1.2]

theorem ratio_log_lower_21 : ((-14838747:ℝ)/20000000) ≤ log ((10:ℝ)/21) := by
  rw [show (10:ℝ)/21 = (((21:ℝ)/10))⁻¹ by norm_num, log_inv]
  linarith [log_21_10.2]

theorem ratio_log_lower_22 : ((-78845737:ℝ)/100000000) ≤ log ((10:ℝ)/22) := by
  rw [show (10:ℝ)/22 = (((11:ℝ)/5))⁻¹ by norm_num, log_inv]
  linarith [log_11_5.2]

theorem ratio_log_lower_23 : ((-83290913:ℝ)/100000000) ≤ log ((10:ℝ)/23) := by
  rw [show (10:ℝ)/23 = (((23:ℝ)/10))⁻¹ by norm_num, log_inv]
  linarith [log_23_10.2]

theorem ratio_log_lower_24 : ((-43773437:ℝ)/50000000) ≤ log ((10:ℝ)/24) := by
  rw [show (10:ℝ)/24 = (((12:ℝ)/5))⁻¹ by norm_num, log_inv]
  linarith [log_12_5.2]

theorem ratio_log_lower_25 : ((-45814537:ℝ)/50000000) ≤ log ((10:ℝ)/25) := by
  rw [show (10:ℝ)/25 = (((5:ℝ)/2))⁻¹ by norm_num, log_inv]
  linarith [log_5_2.2]

theorem ratio_log_lower_26 : ((-19110229:ℝ)/20000000) ≤ log ((10:ℝ)/26) := by
  rw [show (10:ℝ)/26 = (((13:ℝ)/5))⁻¹ by norm_num, log_inv]
  linarith [log_13_5.2]

theorem ratio_log_lower_27 : ((-49662589:ℝ)/50000000) ≤ log ((10:ℝ)/27) := by
  rw [show (10:ℝ)/27 = (((27:ℝ)/10))⁻¹ by norm_num, log_inv]
  linarith [log_27_10.2]

theorem ratio_log_lower_28 : ((-51480971:ℝ)/50000000) ≤ log ((10:ℝ)/28) := by
  rw [show (10:ℝ)/28 = (((14:ℝ)/5))⁻¹ by norm_num, log_inv]
  linarith [log_14_5.2]

theorem ratio_log_lower_29 : ((-53235537:ℝ)/50000000) ≤ log ((10:ℝ)/29) := by
  rw [show (10:ℝ)/29 = (((29:ℝ)/10))⁻¹ by norm_num, log_inv]
  linarith [log_29_10.2]

theorem ratio_log_lower_30 : ((-109861229:ℝ)/100000000) ≤ log ((10:ℝ)/30) := by
  rw [show (10:ℝ)/30 = (((3:ℝ)/1))⁻¹ by norm_num, log_inv]
  linarith [log_3_1.2]

theorem ratio_log_lower_31 : ((-28285053:ℝ)/25000000) ≤ log ((10:ℝ)/31) := by
  rw [show (10:ℝ)/31 = (((31:ℝ)/10))⁻¹ by norm_num, log_inv]
  linarith [log_31_10.2]

end SparseComponent.TotalFamily.Density10
