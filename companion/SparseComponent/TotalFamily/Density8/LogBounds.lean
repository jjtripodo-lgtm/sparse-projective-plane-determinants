import SparseComponent.TotalFamily.PolynomialTools
import SparseComponent.TotalFamily.LogCertificates

namespace SparseComponent.TotalFamily.Density8
open Finset Matrix Real TotalOnes

set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

theorem log_two_precise : ((693147180559:ℝ)/1000000000000) ≤ log (2:ℝ) ∧ log (2:ℝ) ≤ ((8664339757:ℝ)/12500000000) := by
  apply log_interval_of_atanh (2:ℝ) (by norm_num) 16
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_9_8 : ((11778303:ℝ)/100000000) ≤ log ((9:ℝ)/8) ∧ log ((9:ℝ)/8) ≤ ((46009:ℝ)/390625) := by
  apply log_interval_of_atanh ((9:ℝ)/8) (by norm_num) 5
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_8_7 : ((13353139:ℝ)/100000000) ≤ log ((8:ℝ)/7) ∧ log ((8:ℝ)/7) ≤ ((667657:ℝ)/5000000) := by
  apply log_interval_of_atanh ((8:ℝ)/7) (by norm_num) 6
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

theorem log_11_8 : ((31845373:ℝ)/100000000) ≤ log ((11:ℝ)/8) ∧ log ((11:ℝ)/8) ≤ ((15922687:ℝ)/50000000) := by
  apply log_interval_of_atanh ((11:ℝ)/8) (by norm_num) 7
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

theorem log_13_8 : ((48550781:ℝ)/100000000) ≤ log ((13:ℝ)/8) ∧ log ((13:ℝ)/8) ≤ ((24275391:ℝ)/50000000) := by
  apply log_interval_of_atanh ((13:ℝ)/8) (by norm_num) 9
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_7_4 : ((27980789:ℝ)/50000000) ≤ log ((7:ℝ)/4) ∧ log ((7:ℝ)/4) ≤ ((55961579:ℝ)/100000000) := by
  apply log_interval_of_atanh ((7:ℝ)/4) (by norm_num) 10
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_15_8 : ((12572173:ℝ)/20000000) ≤ log ((15:ℝ)/8) ∧ log ((15:ℝ)/8) ≤ ((31430433:ℝ)/50000000) := by
  apply log_interval_of_atanh ((15:ℝ)/8) (by norm_num) 11
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_2_1 : ((34657359:ℝ)/50000000) ≤ log ((2:ℝ)/1) ∧ log ((2:ℝ)/1) ≤ ((69314719:ℝ)/100000000) := by
  apply log_interval_of_atanh ((2:ℝ)/1) (by norm_num) 11
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_17_8 : ((3768859:ℝ)/5000000) ≤ log ((17:ℝ)/8) ∧ log ((17:ℝ)/8) ≤ ((75377181:ℝ)/100000000) := by
  apply log_interval_of_atanh ((17:ℝ)/8) (by norm_num) 12
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_9_4 : ((81093021:ℝ)/100000000) ≤ log ((9:ℝ)/4) ∧ log ((9:ℝ)/4) ≤ ((40546511:ℝ)/50000000) := by
  apply log_interval_of_atanh ((9:ℝ)/4) (by norm_num) 13
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_19_8 : ((86499743:ℝ)/100000000) ≤ log ((19:ℝ)/8) ∧ log ((19:ℝ)/8) ≤ ((2703117:ℝ)/3125000) := by
  apply log_interval_of_atanh ((19:ℝ)/8) (by norm_num) 13
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_5_2 : ((91629073:ℝ)/100000000) ≤ log ((5:ℝ)/2) ∧ log ((5:ℝ)/2) ≤ ((45814537:ℝ)/50000000) := by
  apply log_interval_of_atanh ((5:ℝ)/2) (by norm_num) 13
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_21_8 : ((96508089:ℝ)/100000000) ≤ log ((21:ℝ)/8) ∧ log ((21:ℝ)/8) ≤ ((9650809:ℝ)/10000000) := by
  apply log_interval_of_atanh ((21:ℝ)/8) (by norm_num) 15
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

theorem log_23_8 : ((105605267:ℝ)/100000000) ≤ log ((23:ℝ)/8) ∧ log ((23:ℝ)/8) ≤ ((26401317:ℝ)/25000000) := by
  apply log_interval_of_atanh ((23:ℝ)/8) (by norm_num) 16
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_3_1 : ((27465307:ℝ)/25000000) ≤ log ((3:ℝ)/1) ∧ log ((3:ℝ)/1) ≤ ((109861229:ℝ)/100000000) := by
  apply log_interval_of_atanh ((3:ℝ)/1) (by norm_num) 17
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_25_8 : ((28485857:ℝ)/25000000) ≤ log ((25:ℝ)/8) ∧ log ((25:ℝ)/8) ≤ ((113943429:ℝ)/100000000) := by
  apply log_interval_of_atanh ((25:ℝ)/8) (by norm_num) 17
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_4_1 : ((34657359:ℝ)/25000000) ≤ log ((4:ℝ)/1) ∧ log ((4:ℝ)/1) ≤ ((138629437:ℝ)/100000000) := by
  apply log_interval_of_atanh ((4:ℝ)/1) (by norm_num) 21
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_7_1 : ((97295507:ℝ)/50000000) ≤ log ((7:ℝ)/1) ∧ log ((7:ℝ)/1) ≤ ((38918203:ℝ)/20000000) := by
  have hs : ((111923157587:ℝ)/200000000000) ≤ log ((7:ℝ)/4) ∧ log ((7:ℝ)/4) ≤ ((17487993373:ℝ)/31250000000) := by
    apply log_interval_of_atanh ((7:ℝ)/4) (by norm_num) 13
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have he : log ((7:ℝ)/1) = log ((7:ℝ)/4)+2*log (2:ℝ) := by
    rw [show ((7:ℝ)/1) = ((7:ℝ)/4)*(2:ℝ)^2 by norm_num, log_mul (by norm_num) (by norm_num), log_pow]
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

theorem log_64_7 : ((221297293:ℝ)/100000000) ≤ log ((64:ℝ)/7) ∧ log ((64:ℝ)/7) ≤ ((110648647:ℝ)/50000000) := by
  have hs : ((6458426353:ℝ)/7812500000) ≤ log ((16:ℝ)/7) ∧ log ((16:ℝ)/7) ≤ ((165335714637:ℝ)/200000000000) := by
    apply log_interval_of_atanh ((16:ℝ)/7) (by norm_num) 18
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have he : log ((64:ℝ)/7) = log ((16:ℝ)/7)+2*log (2:ℝ) := by
    rw [show ((64:ℝ)/7) = ((16:ℝ)/7)*(2:ℝ)^2 by norm_num, log_mul (by norm_num) (by norm_num), log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hs.1, hs.2, log_two_precise.1, log_two_precise.2]

theorem gamma_bounds : ((182514133:ℝ)/100000000000) ≤ gamma 8 ∧ gamma 8 ≤ ((91257067:ℝ)/50000000000) := by
  have h := log_64_7
  unfold gamma logGamma
  rw [← log_div (by norm_num : (8:ℝ)^2 ≠ 0) (by norm_num : (8:ℝ)-1 ≠ 0)]
  norm_num at h ⊢
  constructor <;> linarith

theorem ratio_log_lower_2 : ((34657359:ℝ)/25000000) ≤ log ((8:ℝ)/2) := by
  convert log_4_1.1 using 1 <;> norm_num

theorem ratio_log_lower_3 : ((3923317:ℝ)/4000000) ≤ log ((8:ℝ)/3) := by
  convert log_8_3.1 using 1 <;> norm_num

theorem ratio_log_lower_4 : ((34657359:ℝ)/50000000) ≤ log ((8:ℝ)/4) := by
  convert log_2_1.1 using 1 <;> norm_num

theorem ratio_log_lower_5 : ((23500181:ℝ)/50000000) ≤ log ((8:ℝ)/5) := by
  convert log_8_5.1 using 1 <;> norm_num

theorem ratio_log_lower_6 : ((28768207:ℝ)/100000000) ≤ log ((8:ℝ)/6) := by
  convert log_4_3.1 using 1 <;> norm_num

theorem ratio_log_lower_7 : ((13353139:ℝ)/100000000) ≤ log ((8:ℝ)/7) := by
  convert log_8_7.1 using 1 <;> norm_num

theorem ratio_log_lower_8 : ((0:ℝ)/1) ≤ log ((8:ℝ)/8) := by
  norm_num

theorem ratio_log_lower_9 : ((-46009:ℝ)/390625) ≤ log ((8:ℝ)/9) := by
  rw [show (8:ℝ)/9 = (((9:ℝ)/8))⁻¹ by norm_num, log_inv]
  linarith [log_9_8.2]

theorem ratio_log_lower_10 : ((-5578589:ℝ)/25000000) ≤ log ((8:ℝ)/10) := by
  rw [show (8:ℝ)/10 = (((5:ℝ)/4))⁻¹ by norm_num, log_inv]
  linarith [log_5_4.2]

theorem ratio_log_lower_11 : ((-15922687:ℝ)/50000000) ≤ log ((8:ℝ)/11) := by
  rw [show (8:ℝ)/11 = (((11:ℝ)/8))⁻¹ by norm_num, log_inv]
  linarith [log_11_8.2]

theorem ratio_log_lower_12 : ((-40546511:ℝ)/100000000) ≤ log ((8:ℝ)/12) := by
  rw [show (8:ℝ)/12 = (((3:ℝ)/2))⁻¹ by norm_num, log_inv]
  linarith [log_3_2.2]

theorem ratio_log_lower_13 : ((-24275391:ℝ)/50000000) ≤ log ((8:ℝ)/13) := by
  rw [show (8:ℝ)/13 = (((13:ℝ)/8))⁻¹ by norm_num, log_inv]
  linarith [log_13_8.2]

theorem ratio_log_lower_14 : ((-55961579:ℝ)/100000000) ≤ log ((8:ℝ)/14) := by
  rw [show (8:ℝ)/14 = (((7:ℝ)/4))⁻¹ by norm_num, log_inv]
  linarith [log_7_4.2]

theorem ratio_log_lower_15 : ((-31430433:ℝ)/50000000) ≤ log ((8:ℝ)/15) := by
  rw [show (8:ℝ)/15 = (((15:ℝ)/8))⁻¹ by norm_num, log_inv]
  linarith [log_15_8.2]

theorem ratio_log_lower_16 : ((-69314719:ℝ)/100000000) ≤ log ((8:ℝ)/16) := by
  rw [show (8:ℝ)/16 = (((2:ℝ)/1))⁻¹ by norm_num, log_inv]
  linarith [log_2_1.2]

theorem ratio_log_lower_17 : ((-75377181:ℝ)/100000000) ≤ log ((8:ℝ)/17) := by
  rw [show (8:ℝ)/17 = (((17:ℝ)/8))⁻¹ by norm_num, log_inv]
  linarith [log_17_8.2]

theorem ratio_log_lower_18 : ((-40546511:ℝ)/50000000) ≤ log ((8:ℝ)/18) := by
  rw [show (8:ℝ)/18 = (((9:ℝ)/4))⁻¹ by norm_num, log_inv]
  linarith [log_9_4.2]

theorem ratio_log_lower_19 : ((-2703117:ℝ)/3125000) ≤ log ((8:ℝ)/19) := by
  rw [show (8:ℝ)/19 = (((19:ℝ)/8))⁻¹ by norm_num, log_inv]
  linarith [log_19_8.2]

theorem ratio_log_lower_20 : ((-45814537:ℝ)/50000000) ≤ log ((8:ℝ)/20) := by
  rw [show (8:ℝ)/20 = (((5:ℝ)/2))⁻¹ by norm_num, log_inv]
  linarith [log_5_2.2]

theorem ratio_log_lower_21 : ((-9650809:ℝ)/10000000) ≤ log ((8:ℝ)/21) := by
  rw [show (8:ℝ)/21 = (((21:ℝ)/8))⁻¹ by norm_num, log_inv]
  linarith [log_21_8.2]

theorem ratio_log_lower_22 : ((-25290023:ℝ)/25000000) ≤ log ((8:ℝ)/22) := by
  rw [show (8:ℝ)/22 = (((11:ℝ)/4))⁻¹ by norm_num, log_inv]
  linarith [log_11_4.2]

theorem ratio_log_lower_23 : ((-26401317:ℝ)/25000000) ≤ log ((8:ℝ)/23) := by
  rw [show (8:ℝ)/23 = (((23:ℝ)/8))⁻¹ by norm_num, log_inv]
  linarith [log_23_8.2]

theorem ratio_log_lower_24 : ((-109861229:ℝ)/100000000) ≤ log ((8:ℝ)/24) := by
  rw [show (8:ℝ)/24 = (((3:ℝ)/1))⁻¹ by norm_num, log_inv]
  linarith [log_3_1.2]

theorem ratio_log_lower_25 : ((-113943429:ℝ)/100000000) ≤ log ((8:ℝ)/25) := by
  rw [show (8:ℝ)/25 = (((25:ℝ)/8))⁻¹ by norm_num, log_inv]
  linarith [log_25_8.2]

end SparseComponent.TotalFamily.Density8
