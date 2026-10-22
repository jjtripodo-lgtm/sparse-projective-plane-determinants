import SparseComponent.TotalFamily.PolynomialTools
import SparseComponent.TotalFamily.LogCertificates

namespace SparseComponent.TotalFamily.Density7
open Finset Matrix Real TotalOnes

set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

theorem log_8_7 : ((13353139:ℝ)/100000000) ≤ log ((8:ℝ)/7) ∧ log ((8:ℝ)/7) ≤ ((667657:ℝ)/5000000) := by
  apply log_interval_of_atanh ((8:ℝ)/7) (by norm_num) 32
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_7_6 : ((15415067:ℝ)/100000000) ≤ log ((7:ℝ)/6) ∧ log ((7:ℝ)/6) ≤ ((3853767:ℝ)/25000000) := by
  apply log_interval_of_atanh ((7:ℝ)/6) (by norm_num) 32
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_9_7 : ((12565721:ℝ)/50000000) ≤ log ((9:ℝ)/7) ∧ log ((9:ℝ)/7) ≤ ((25131443:ℝ)/100000000) := by
  apply log_interval_of_atanh ((9:ℝ)/7) (by norm_num) 32
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_7_5 : ((33647223:ℝ)/100000000) ≤ log ((7:ℝ)/5) ∧ log ((7:ℝ)/5) ≤ ((4205903:ℝ)/12500000) := by
  apply log_interval_of_atanh ((7:ℝ)/5) (by norm_num) 32
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_10_7 : ((17833747:ℝ)/50000000) ≤ log ((10:ℝ)/7) ∧ log ((10:ℝ)/7) ≤ ((7133499:ℝ)/20000000) := by
  apply log_interval_of_atanh ((10:ℝ)/7) (by norm_num) 32
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_11_7 : ((2824907:ℝ)/6250000) ≤ log ((11:ℝ)/7) ∧ log ((11:ℝ)/7) ≤ ((45198513:ℝ)/100000000) := by
  apply log_interval_of_atanh ((11:ℝ)/7) (by norm_num) 32
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_12_7 : ((1077993:ℝ)/2000000) ≤ log ((12:ℝ)/7) ∧ log ((12:ℝ)/7) ≤ ((53899651:ℝ)/100000000) := by
  apply log_interval_of_atanh ((12:ℝ)/7) (by norm_num) 32
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_7_4 : ((27980789:ℝ)/50000000) ≤ log ((7:ℝ)/4) ∧ log ((7:ℝ)/4) ≤ ((55961579:ℝ)/100000000) := by
  apply log_interval_of_atanh ((7:ℝ)/4) (by norm_num) 32
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_13_7 : ((773799:ℝ)/1250000) ≤ log ((13:ℝ)/7) ∧ log ((13:ℝ)/7) ≤ ((61903921:ℝ)/100000000) := by
  apply log_interval_of_atanh ((13:ℝ)/7) (by norm_num) 32
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_2_1 : ((34657359:ℝ)/50000000) ≤ log ((2:ℝ)/1) ∧ log ((2:ℝ)/1) ≤ ((69314719:ℝ)/100000000) := by
  apply log_interval_of_atanh ((2:ℝ)/1) (by norm_num) 32
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_15_7 : ((15242801:ℝ)/20000000) ≤ log ((15:ℝ)/7) ∧ log ((15:ℝ)/7) ≤ ((38107003:ℝ)/50000000) := by
  apply log_interval_of_atanh ((15:ℝ)/7) (by norm_num) 32
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_16_7 : ((82667857:ℝ)/100000000) ≤ log ((16:ℝ)/7) ∧ log ((16:ℝ)/7) ≤ ((41333929:ℝ)/50000000) := by
  apply log_interval_of_atanh ((16:ℝ)/7) (by norm_num) 32
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_7_3 : ((42364893:ℝ)/50000000) ≤ log ((7:ℝ)/3) ∧ log ((7:ℝ)/3) ≤ ((84729787:ℝ)/100000000) := by
  apply log_interval_of_atanh ((7:ℝ)/3) (by norm_num) 32
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_17_7 : ((88730319:ℝ)/100000000) ≤ log ((17:ℝ)/7) ∧ log ((17:ℝ)/7) ≤ ((1109129:ℝ)/1250000) := by
  apply log_interval_of_atanh ((17:ℝ)/7) (by norm_num) 32
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_18_7 : ((1180577:ℝ)/1250000) ≤ log ((18:ℝ)/7) ∧ log ((18:ℝ)/7) ≤ ((94446161:ℝ)/100000000) := by
  apply log_interval_of_atanh ((18:ℝ)/7) (by norm_num) 32
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_19_7 : ((99852883:ℝ)/100000000) ≤ log ((19:ℝ)/7) ∧ log ((19:ℝ)/7) ≤ ((24963221:ℝ)/25000000) := by
  apply log_interval_of_atanh ((19:ℝ)/7) (by norm_num) 32
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_20_7 : ((26245553:ℝ)/25000000) ≤ log ((20:ℝ)/7) ∧ log ((20:ℝ)/7) ≤ ((104982213:ℝ)/100000000) := by
  apply log_interval_of_atanh ((20:ℝ)/7) (by norm_num) 32
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_3_1 : ((27465307:ℝ)/25000000) ≤ log ((3:ℝ)/1) ∧ log ((3:ℝ)/1) ≤ ((109861229:ℝ)/100000000) := by
  apply log_interval_of_atanh ((3:ℝ)/1) (by norm_num) 32
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_22_7 : ((11451323:ℝ)/10000000) ≤ log ((22:ℝ)/7) ∧ log ((22:ℝ)/7) ≤ ((114513231:ℝ)/100000000) := by
  apply log_interval_of_atanh ((22:ℝ)/7) (by norm_num) 32
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_7_2 : ((15659537:ℝ)/12500000) ≤ log ((7:ℝ)/2) ∧ log ((7:ℝ)/2) ≤ ((125276297:ℝ)/100000000) := by
  apply log_interval_of_atanh ((7:ℝ)/2) (by norm_num) 32
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_6_1 : ((89587973:ℝ)/50000000) ≤ log ((6:ℝ)/1) ∧ log ((6:ℝ)/1) ≤ ((179175947:ℝ)/100000000) := by
  apply log_interval_of_atanh ((6:ℝ)/1) (by norm_num) 96
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_7_1 : ((97295507:ℝ)/50000000) ≤ log ((7:ℝ)/1) ∧ log ((7:ℝ)/1) ≤ ((38918203:ℝ)/20000000) := by
  apply log_interval_of_atanh ((7:ℝ)/1) (by norm_num) 96
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_49_6 : ((105003041:ℝ)/50000000) ≤ log ((49:ℝ)/6) ∧ log ((49:ℝ)/6) ≤ ((210006083:ℝ)/100000000) := by
  apply log_interval_of_atanh ((49:ℝ)/6) (by norm_num) 96
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem gamma_bounds : ((274018703:ℝ)/100000000000) ≤ gamma 7 ∧ gamma 7 ≤ ((54803741:ℝ)/20000000000) := by
  have h := log_49_6
  unfold gamma logGamma
  rw [← log_div (by norm_num : (7:ℝ)^2 ≠ 0) (by norm_num : (7:ℝ)-1 ≠ 0)]
  norm_num at h ⊢
  constructor <;> linarith

theorem ratio_log_lower_2 : ((15659537:ℝ)/12500000) ≤ log ((7:ℝ)/2) := by
  convert log_7_2.1 using 1 <;> norm_num

theorem ratio_log_lower_3 : ((42364893:ℝ)/50000000) ≤ log ((7:ℝ)/3) := by
  convert log_7_3.1 using 1 <;> norm_num

theorem ratio_log_lower_4 : ((27980789:ℝ)/50000000) ≤ log ((7:ℝ)/4) := by
  convert log_7_4.1 using 1 <;> norm_num

theorem ratio_log_lower_5 : ((33647223:ℝ)/100000000) ≤ log ((7:ℝ)/5) := by
  convert log_7_5.1 using 1 <;> norm_num

theorem ratio_log_lower_6 : ((15415067:ℝ)/100000000) ≤ log ((7:ℝ)/6) := by
  convert log_7_6.1 using 1 <;> norm_num

theorem ratio_log_lower_7 : ((0:ℝ)/1) ≤ log ((7:ℝ)/7) := by
  norm_num

theorem ratio_log_lower_8 : ((-667657:ℝ)/5000000) ≤ log ((7:ℝ)/8) := by
  rw [show (7:ℝ)/8 = (((8:ℝ)/7))⁻¹ by norm_num, log_inv]
  linarith [log_8_7.2]

theorem ratio_log_lower_9 : ((-25131443:ℝ)/100000000) ≤ log ((7:ℝ)/9) := by
  rw [show (7:ℝ)/9 = (((9:ℝ)/7))⁻¹ by norm_num, log_inv]
  linarith [log_9_7.2]

theorem ratio_log_lower_10 : ((-7133499:ℝ)/20000000) ≤ log ((7:ℝ)/10) := by
  rw [show (7:ℝ)/10 = (((10:ℝ)/7))⁻¹ by norm_num, log_inv]
  linarith [log_10_7.2]

theorem ratio_log_lower_11 : ((-45198513:ℝ)/100000000) ≤ log ((7:ℝ)/11) := by
  rw [show (7:ℝ)/11 = (((11:ℝ)/7))⁻¹ by norm_num, log_inv]
  linarith [log_11_7.2]

theorem ratio_log_lower_12 : ((-53899651:ℝ)/100000000) ≤ log ((7:ℝ)/12) := by
  rw [show (7:ℝ)/12 = (((12:ℝ)/7))⁻¹ by norm_num, log_inv]
  linarith [log_12_7.2]

theorem ratio_log_lower_13 : ((-61903921:ℝ)/100000000) ≤ log ((7:ℝ)/13) := by
  rw [show (7:ℝ)/13 = (((13:ℝ)/7))⁻¹ by norm_num, log_inv]
  linarith [log_13_7.2]

theorem ratio_log_lower_14 : ((-69314719:ℝ)/100000000) ≤ log ((7:ℝ)/14) := by
  rw [show (7:ℝ)/14 = (((2:ℝ)/1))⁻¹ by norm_num, log_inv]
  linarith [log_2_1.2]

theorem ratio_log_lower_15 : ((-38107003:ℝ)/50000000) ≤ log ((7:ℝ)/15) := by
  rw [show (7:ℝ)/15 = (((15:ℝ)/7))⁻¹ by norm_num, log_inv]
  linarith [log_15_7.2]

theorem ratio_log_lower_16 : ((-41333929:ℝ)/50000000) ≤ log ((7:ℝ)/16) := by
  rw [show (7:ℝ)/16 = (((16:ℝ)/7))⁻¹ by norm_num, log_inv]
  linarith [log_16_7.2]

theorem ratio_log_lower_17 : ((-1109129:ℝ)/1250000) ≤ log ((7:ℝ)/17) := by
  rw [show (7:ℝ)/17 = (((17:ℝ)/7))⁻¹ by norm_num, log_inv]
  linarith [log_17_7.2]

theorem ratio_log_lower_18 : ((-94446161:ℝ)/100000000) ≤ log ((7:ℝ)/18) := by
  rw [show (7:ℝ)/18 = (((18:ℝ)/7))⁻¹ by norm_num, log_inv]
  linarith [log_18_7.2]

theorem ratio_log_lower_19 : ((-24963221:ℝ)/25000000) ≤ log ((7:ℝ)/19) := by
  rw [show (7:ℝ)/19 = (((19:ℝ)/7))⁻¹ by norm_num, log_inv]
  linarith [log_19_7.2]

theorem ratio_log_lower_20 : ((-104982213:ℝ)/100000000) ≤ log ((7:ℝ)/20) := by
  rw [show (7:ℝ)/20 = (((20:ℝ)/7))⁻¹ by norm_num, log_inv]
  linarith [log_20_7.2]

theorem ratio_log_lower_21 : ((-109861229:ℝ)/100000000) ≤ log ((7:ℝ)/21) := by
  rw [show (7:ℝ)/21 = (((3:ℝ)/1))⁻¹ by norm_num, log_inv]
  linarith [log_3_1.2]

theorem ratio_log_lower_22 : ((-114513231:ℝ)/100000000) ≤ log ((7:ℝ)/22) := by
  rw [show (7:ℝ)/22 = (((22:ℝ)/7))⁻¹ by norm_num, log_inv]
  linarith [log_22_7.2]

end SparseComponent.TotalFamily.Density7
