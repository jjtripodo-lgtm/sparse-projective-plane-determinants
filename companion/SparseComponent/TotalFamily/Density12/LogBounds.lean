import SparseComponent.TotalFamily.Density8.LogBounds
import SparseComponent.TotalFamily.PolynomialTools
import SparseComponent.TotalFamily.LogCertificates

namespace SparseComponent.TotalFamily.Density12
open Finset Matrix Real TotalOnes

set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

theorem log_two_precise : ((693147180559:ℝ)/1000000000000) ≤ log (2:ℝ) ∧ log (2:ℝ) ≤ ((8664339757:ℝ)/12500000000) := by
  exact Density8.log_two_precise

theorem log_13_12 : ((800427:ℝ)/10000000) ≤ log ((13:ℝ)/12) ∧ log ((13:ℝ)/12) ≤ ((8004271:ℝ)/100000000) := by
  apply log_interval_of_atanh ((13:ℝ)/12) (by norm_num) 5
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_12_11 : ((8701137:ℝ)/100000000) ≤ log ((12:ℝ)/11) ∧ log ((12:ℝ)/11) ≤ ((4350569:ℝ)/50000000) := by
  apply log_interval_of_atanh ((12:ℝ)/11) (by norm_num) 5
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_7_6 : ((15415067:ℝ)/100000000) ≤ log ((7:ℝ)/6) ∧ log ((7:ℝ)/6) ≤ ((3853767:ℝ)/25000000) := by
  apply log_interval_of_atanh ((7:ℝ)/6) (by norm_num) 6
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

theorem log_4_3 : ((28768207:ℝ)/100000000) ≤ log ((4:ℝ)/3) ∧ log ((4:ℝ)/3) ≤ ((1798013:ℝ)/6250000) := by
  apply log_interval_of_atanh ((4:ℝ)/3) (by norm_num) 7
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_17_12 : ((34830669:ℝ)/100000000) ≤ log ((17:ℝ)/12) ∧ log ((17:ℝ)/12) ≤ ((3483067:ℝ)/10000000) := by
  apply log_interval_of_atanh ((17:ℝ)/12) (by norm_num) 8
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_3_2 : ((4054651:ℝ)/10000000) ≤ log ((3:ℝ)/2) ∧ log ((3:ℝ)/2) ≤ ((40546511:ℝ)/100000000) := by
  apply log_interval_of_atanh ((3:ℝ)/2) (by norm_num) 8
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_19_12 : ((2872077:ℝ)/6250000) ≤ log ((19:ℝ)/12) ∧ log ((19:ℝ)/12) ≤ ((45953233:ℝ)/100000000) := by
  apply log_interval_of_atanh ((19:ℝ)/12) (by norm_num) 9
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_5_3 : ((25541281:ℝ)/50000000) ≤ log ((5:ℝ)/3) ∧ log ((5:ℝ)/3) ≤ ((51082563:ℝ)/100000000) := by
  apply log_interval_of_atanh ((5:ℝ)/3) (by norm_num) 9
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_12_7 : ((1077993:ℝ)/2000000) ≤ log ((12:ℝ)/7) ∧ log ((12:ℝ)/7) ≤ ((53899651:ℝ)/100000000) := by
  apply log_interval_of_atanh ((12:ℝ)/7) (by norm_num) 9
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_7_4 : ((27980789:ℝ)/50000000) ≤ log ((7:ℝ)/4) ∧ log ((7:ℝ)/4) ≤ ((55961579:ℝ)/100000000) := by
  apply log_interval_of_atanh ((7:ℝ)/4) (by norm_num) 10
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_11_6 : ((3030679:ℝ)/5000000) ≤ log ((11:ℝ)/6) ∧ log ((11:ℝ)/6) ≤ ((60613581:ℝ)/100000000) := by
  apply log_interval_of_atanh ((11:ℝ)/6) (by norm_num) 10
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_23_12 : ((16264689:ℝ)/25000000) ≤ log ((23:ℝ)/12) ∧ log ((23:ℝ)/12) ≤ ((65058757:ℝ)/100000000) := by
  apply log_interval_of_atanh ((23:ℝ)/12) (by norm_num) 11
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_2_1 : ((34657359:ℝ)/50000000) ≤ log ((2:ℝ)/1) ∧ log ((2:ℝ)/1) ≤ ((69314719:ℝ)/100000000) := by
  apply log_interval_of_atanh ((2:ℝ)/1) (by norm_num) 11
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_25_12 : ((73396917:ℝ)/100000000) ≤ log ((25:ℝ)/12) ∧ log ((25:ℝ)/12) ≤ ((36698459:ℝ)/50000000) := by
  apply log_interval_of_atanh ((25:ℝ)/12) (by norm_num) 12
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_13_6 : ((19329747:ℝ)/25000000) ≤ log ((13:ℝ)/6) ∧ log ((13:ℝ)/6) ≤ ((77318989:ℝ)/100000000) := by
  apply log_interval_of_atanh ((13:ℝ)/6) (by norm_num) 12
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

theorem log_12_5 : ((87546873:ℝ)/100000000) ≤ log ((12:ℝ)/5) ∧ log ((12:ℝ)/5) ≤ ((43773437:ℝ)/50000000) := by
  apply log_interval_of_atanh ((12:ℝ)/5) (by norm_num) 14
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_29_12 : ((44119459:ℝ)/50000000) ≤ log ((29:ℝ)/12) ∧ log ((29:ℝ)/12) ≤ ((88238919:ℝ)/100000000) := by
  apply log_interval_of_atanh ((29:ℝ)/12) (by norm_num) 13
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_5_2 : ((91629073:ℝ)/100000000) ≤ log ((5:ℝ)/2) ∧ log ((5:ℝ)/2) ≤ ((45814537:ℝ)/50000000) := by
  apply log_interval_of_atanh ((5:ℝ)/2) (by norm_num) 13
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_31_12 : ((18981611:ℝ)/20000000) ≤ log ((31:ℝ)/12) ∧ log ((31:ℝ)/12) ≤ ((11863507:ℝ)/12500000) := by
  apply log_interval_of_atanh ((31:ℝ)/12) (by norm_num) 14
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_8_3 : ((3923317:ℝ)/4000000) ≤ log ((8:ℝ)/3) ∧ log ((8:ℝ)/3) ≤ ((49041463:ℝ)/50000000) := by
  apply log_interval_of_atanh ((8:ℝ)/3) (by norm_num) 14
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_11_4 : ((101160091:ℝ)/100000000) ≤ log ((11:ℝ)/4) ∧ log ((11:ℝ)/4) ≤ ((25290023:ℝ)/25000000) := by
  apply log_interval_of_atanh ((11:ℝ)/4) (by norm_num) 15
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_17_6 : ((104145387:ℝ)/100000000) ≤ log ((17:ℝ)/6) ∧ log ((17:ℝ)/6) ≤ ((26036347:ℝ)/25000000) := by
  apply log_interval_of_atanh ((17:ℝ)/6) (by norm_num) 16
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_35_12 : ((107044141:ℝ)/100000000) ≤ log ((35:ℝ)/12) ∧ log ((35:ℝ)/12) ≤ ((53522071:ℝ)/50000000) := by
  apply log_interval_of_atanh ((35:ℝ)/12) (by norm_num) 16
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_3_1 : ((27465307:ℝ)/25000000) ≤ log ((3:ℝ)/1) ∧ log ((3:ℝ)/1) ≤ ((109861229:ℝ)/100000000) := by
  apply log_interval_of_atanh ((3:ℝ)/1) (by norm_num) 17
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_37_12 : ((56300563:ℝ)/50000000) ≤ log ((37:ℝ)/12) ∧ log ((37:ℝ)/12) ≤ ((112601127:ℝ)/100000000) := by
  apply log_interval_of_atanh ((37:ℝ)/12) (by norm_num) 17
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_4_1 : ((34657359:ℝ)/25000000) ≤ log ((4:ℝ)/1) ∧ log ((4:ℝ)/1) ≤ ((138629437:ℝ)/100000000) := by
  apply log_interval_of_atanh ((4:ℝ)/1) (by norm_num) 21
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

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

theorem log_12_1 : ((31061333:ℝ)/12500000) ≤ log ((12:ℝ)/1) ∧ log ((12:ℝ)/1) ≤ ((49698133:ℝ)/20000000) := by
  have hs : ((274653072167:ℝ)/250000000000) ≤ log ((3:ℝ)/1) ∧ log ((3:ℝ)/1) ≤ ((1098612288669:ℝ)/1000000000000) := by
    apply log_interval_of_atanh ((3:ℝ)/1) (by norm_num) 23
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have he : log ((12:ℝ)/1) = log ((3:ℝ)/1)+2*log (2:ℝ) := by
    rw [show ((12:ℝ)/1) = ((3:ℝ)/1)*(2:ℝ)^2 by norm_num, log_mul (by norm_num) (by norm_num), log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hs.1, hs.2, log_two_precise.1, log_two_precise.2]

theorem log_144_11 : ((128595901:ℝ)/50000000) ≤ log ((144:ℝ)/11) ∧ log ((144:ℝ)/11) ≤ ((257191803:ℝ)/100000000) := by
  have hs : ((1185623665657:ℝ)/1000000000000) ≤ log ((36:ℝ)/11) ∧ log ((36:ℝ)/11) ≤ ((592811832829:ℝ)/500000000000) := by
    apply log_interval_of_atanh ((36:ℝ)/11) (by norm_num) 26
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have he : log ((144:ℝ)/11) = log ((36:ℝ)/11)+2*log (2:ℝ) := by
    rw [show ((144:ℝ)/11) = ((36:ℝ)/11)*(2:ℝ)^2 by norm_num, log_mul (by norm_num) (by norm_num), log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hs.1, hs.2, log_two_precise.1, log_two_precise.2]

theorem gamma_bounds : ((53813053:ℝ)/100000000000) ≤ gamma 12 ∧ gamma 12 ≤ ((26906527:ℝ)/50000000000) := by
  have h := log_144_11
  unfold gamma logGamma
  rw [← log_div (by norm_num : (12:ℝ)^2 ≠ 0) (by norm_num : (12:ℝ)-1 ≠ 0)]
  norm_num at h ⊢
  constructor <;> linarith

theorem ratio_log_lower_3 : ((34657359:ℝ)/25000000) ≤ log ((12:ℝ)/3) := by
  convert log_4_1.1 using 1 <;> norm_num

theorem ratio_log_lower_4 : ((27465307:ℝ)/25000000) ≤ log ((12:ℝ)/4) := by
  convert log_3_1.1 using 1 <;> norm_num

theorem ratio_log_lower_5 : ((87546873:ℝ)/100000000) ≤ log ((12:ℝ)/5) := by
  convert log_12_5.1 using 1 <;> norm_num

theorem ratio_log_lower_6 : ((34657359:ℝ)/50000000) ≤ log ((12:ℝ)/6) := by
  convert log_2_1.1 using 1 <;> norm_num

theorem ratio_log_lower_7 : ((1077993:ℝ)/2000000) ≤ log ((12:ℝ)/7) := by
  convert log_12_7.1 using 1 <;> norm_num

theorem ratio_log_lower_8 : ((4054651:ℝ)/10000000) ≤ log ((12:ℝ)/8) := by
  convert log_3_2.1 using 1 <;> norm_num

theorem ratio_log_lower_9 : ((28768207:ℝ)/100000000) ≤ log ((12:ℝ)/9) := by
  convert log_4_3.1 using 1 <;> norm_num

theorem ratio_log_lower_10 : ((3646431:ℝ)/20000000) ≤ log ((12:ℝ)/10) := by
  convert log_6_5.1 using 1 <;> norm_num

theorem ratio_log_lower_11 : ((8701137:ℝ)/100000000) ≤ log ((12:ℝ)/11) := by
  convert log_12_11.1 using 1 <;> norm_num

theorem ratio_log_lower_12 : ((0:ℝ)/1) ≤ log ((12:ℝ)/12) := by
  norm_num

theorem ratio_log_lower_13 : ((-8004271:ℝ)/100000000) ≤ log ((12:ℝ)/13) := by
  rw [show (12:ℝ)/13 = (((13:ℝ)/12))⁻¹ by norm_num, log_inv]
  linarith [log_13_12.2]

theorem ratio_log_lower_14 : ((-3853767:ℝ)/25000000) ≤ log ((12:ℝ)/14) := by
  rw [show (12:ℝ)/14 = (((7:ℝ)/6))⁻¹ by norm_num, log_inv]
  linarith [log_7_6.2]

theorem ratio_log_lower_15 : ((-5578589:ℝ)/25000000) ≤ log ((12:ℝ)/15) := by
  rw [show (12:ℝ)/15 = (((5:ℝ)/4))⁻¹ by norm_num, log_inv]
  linarith [log_5_4.2]

theorem ratio_log_lower_16 : ((-1798013:ℝ)/6250000) ≤ log ((12:ℝ)/16) := by
  rw [show (12:ℝ)/16 = (((4:ℝ)/3))⁻¹ by norm_num, log_inv]
  linarith [log_4_3.2]

theorem ratio_log_lower_17 : ((-3483067:ℝ)/10000000) ≤ log ((12:ℝ)/17) := by
  rw [show (12:ℝ)/17 = (((17:ℝ)/12))⁻¹ by norm_num, log_inv]
  linarith [log_17_12.2]

theorem ratio_log_lower_18 : ((-40546511:ℝ)/100000000) ≤ log ((12:ℝ)/18) := by
  rw [show (12:ℝ)/18 = (((3:ℝ)/2))⁻¹ by norm_num, log_inv]
  linarith [log_3_2.2]

theorem ratio_log_lower_19 : ((-45953233:ℝ)/100000000) ≤ log ((12:ℝ)/19) := by
  rw [show (12:ℝ)/19 = (((19:ℝ)/12))⁻¹ by norm_num, log_inv]
  linarith [log_19_12.2]

theorem ratio_log_lower_20 : ((-51082563:ℝ)/100000000) ≤ log ((12:ℝ)/20) := by
  rw [show (12:ℝ)/20 = (((5:ℝ)/3))⁻¹ by norm_num, log_inv]
  linarith [log_5_3.2]

theorem ratio_log_lower_21 : ((-55961579:ℝ)/100000000) ≤ log ((12:ℝ)/21) := by
  rw [show (12:ℝ)/21 = (((7:ℝ)/4))⁻¹ by norm_num, log_inv]
  linarith [log_7_4.2]

theorem ratio_log_lower_22 : ((-60613581:ℝ)/100000000) ≤ log ((12:ℝ)/22) := by
  rw [show (12:ℝ)/22 = (((11:ℝ)/6))⁻¹ by norm_num, log_inv]
  linarith [log_11_6.2]

theorem ratio_log_lower_23 : ((-65058757:ℝ)/100000000) ≤ log ((12:ℝ)/23) := by
  rw [show (12:ℝ)/23 = (((23:ℝ)/12))⁻¹ by norm_num, log_inv]
  linarith [log_23_12.2]

theorem ratio_log_lower_24 : ((-69314719:ℝ)/100000000) ≤ log ((12:ℝ)/24) := by
  rw [show (12:ℝ)/24 = (((2:ℝ)/1))⁻¹ by norm_num, log_inv]
  linarith [log_2_1.2]

theorem ratio_log_lower_25 : ((-36698459:ℝ)/50000000) ≤ log ((12:ℝ)/25) := by
  rw [show (12:ℝ)/25 = (((25:ℝ)/12))⁻¹ by norm_num, log_inv]
  linarith [log_25_12.2]

theorem ratio_log_lower_26 : ((-77318989:ℝ)/100000000) ≤ log ((12:ℝ)/26) := by
  rw [show (12:ℝ)/26 = (((13:ℝ)/6))⁻¹ by norm_num, log_inv]
  linarith [log_13_6.2]

theorem ratio_log_lower_27 : ((-40546511:ℝ)/50000000) ≤ log ((12:ℝ)/27) := by
  rw [show (12:ℝ)/27 = (((9:ℝ)/4))⁻¹ by norm_num, log_inv]
  linarith [log_9_4.2]

theorem ratio_log_lower_28 : ((-84729787:ℝ)/100000000) ≤ log ((12:ℝ)/28) := by
  rw [show (12:ℝ)/28 = (((7:ℝ)/3))⁻¹ by norm_num, log_inv]
  linarith [log_7_3.2]

theorem ratio_log_lower_29 : ((-88238919:ℝ)/100000000) ≤ log ((12:ℝ)/29) := by
  rw [show (12:ℝ)/29 = (((29:ℝ)/12))⁻¹ by norm_num, log_inv]
  linarith [log_29_12.2]

theorem ratio_log_lower_30 : ((-45814537:ℝ)/50000000) ≤ log ((12:ℝ)/30) := by
  rw [show (12:ℝ)/30 = (((5:ℝ)/2))⁻¹ by norm_num, log_inv]
  linarith [log_5_2.2]

theorem ratio_log_lower_31 : ((-11863507:ℝ)/12500000) ≤ log ((12:ℝ)/31) := by
  rw [show (12:ℝ)/31 = (((31:ℝ)/12))⁻¹ by norm_num, log_inv]
  linarith [log_31_12.2]

theorem ratio_log_lower_32 : ((-49041463:ℝ)/50000000) ≤ log ((12:ℝ)/32) := by
  rw [show (12:ℝ)/32 = (((8:ℝ)/3))⁻¹ by norm_num, log_inv]
  linarith [log_8_3.2]

theorem ratio_log_lower_33 : ((-25290023:ℝ)/25000000) ≤ log ((12:ℝ)/33) := by
  rw [show (12:ℝ)/33 = (((11:ℝ)/4))⁻¹ by norm_num, log_inv]
  linarith [log_11_4.2]

theorem ratio_log_lower_34 : ((-26036347:ℝ)/25000000) ≤ log ((12:ℝ)/34) := by
  rw [show (12:ℝ)/34 = (((17:ℝ)/6))⁻¹ by norm_num, log_inv]
  linarith [log_17_6.2]

theorem ratio_log_lower_35 : ((-53522071:ℝ)/50000000) ≤ log ((12:ℝ)/35) := by
  rw [show (12:ℝ)/35 = (((35:ℝ)/12))⁻¹ by norm_num, log_inv]
  linarith [log_35_12.2]

theorem ratio_log_lower_36 : ((-109861229:ℝ)/100000000) ≤ log ((12:ℝ)/36) := by
  rw [show (12:ℝ)/36 = (((3:ℝ)/1))⁻¹ by norm_num, log_inv]
  linarith [log_3_1.2]

theorem ratio_log_lower_37 : ((-112601127:ℝ)/100000000) ≤ log ((12:ℝ)/37) := by
  rw [show (12:ℝ)/37 = (((37:ℝ)/12))⁻¹ by norm_num, log_inv]
  linarith [log_37_12.2]

end SparseComponent.TotalFamily.Density12
