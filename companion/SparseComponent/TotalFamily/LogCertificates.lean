import SparseComponent.TotalFamily.Separable
import Mathlib.Tactic.IntervalCases

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SparseComponent.TotalFamily.Certificates
open Finset Real TotalOnes

theorem log_7_6_bounds : (3083:ℝ)/20000 ≤ log ((7:ℝ)/6) ∧ log ((7:ℝ)/6) ≤ (154151:ℝ)/1000000 := by
  apply log_interval_of_atanh ((7:ℝ)/6) (by norm_num) 24
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_6_5_bounds : (182321:ℝ)/1000000 ≤ log ((6:ℝ)/5) ∧ log ((6:ℝ)/5) ≤ (91161:ℝ)/500000 := by
  apply log_interval_of_atanh ((6:ℝ)/5) (by norm_num) 24
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_5_4_bounds : (223143:ℝ)/1000000 ≤ log ((5:ℝ)/4) ∧ log ((5:ℝ)/4) ≤ (27893:ℝ)/125000 := by
  apply log_interval_of_atanh ((5:ℝ)/4) (by norm_num) 24
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_4_3_bounds : (143841:ℝ)/500000 ≤ log ((4:ℝ)/3) ∧ log ((4:ℝ)/3) ≤ (287683:ℝ)/1000000 := by
  apply log_interval_of_atanh ((4:ℝ)/3) (by norm_num) 24
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_7_5_bounds : (42059:ℝ)/125000 ≤ log ((7:ℝ)/5) ∧ log ((7:ℝ)/5) ≤ (336473:ℝ)/1000000 := by
  apply log_interval_of_atanh ((7:ℝ)/5) (by norm_num) 24
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_3_2_bounds : (81093:ℝ)/200000 ≤ log ((3:ℝ)/2) ∧ log ((3:ℝ)/2) ≤ (202733:ℝ)/500000 := by
  apply log_interval_of_atanh ((3:ℝ)/2) (by norm_num) 24
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_8_5_bounds : (470003:ℝ)/1000000 ≤ log ((8:ℝ)/5) ∧ log ((8:ℝ)/5) ≤ (117501:ℝ)/250000 := by
  apply log_interval_of_atanh ((8:ℝ)/5) (by norm_num) 24
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_5_3_bounds : (20433:ℝ)/40000 ≤ log ((5:ℝ)/3) ∧ log ((5:ℝ)/3) ≤ (255413:ℝ)/500000 := by
  apply log_interval_of_atanh ((5:ℝ)/3) (by norm_num) 24
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_7_4_bounds : (111923:ℝ)/200000 ≤ log ((7:ℝ)/4) ∧ log ((7:ℝ)/4) ≤ (8744:ℝ)/15625 := by
  apply log_interval_of_atanh ((7:ℝ)/4) (by norm_num) 24
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_9_5_bounds : (293893:ℝ)/500000 ≤ log ((9:ℝ)/5) ∧ log ((9:ℝ)/5) ≤ (587787:ℝ)/1000000 := by
  apply log_interval_of_atanh ((9:ℝ)/5) (by norm_num) 24
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_11_6_bounds : (121227:ℝ)/200000 ≤ log ((11:ℝ)/6) ∧ log ((11:ℝ)/6) ≤ (75767:ℝ)/125000 := by
  apply log_interval_of_atanh ((11:ℝ)/6) (by norm_num) 24
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_2_1_bounds : (693147:ℝ)/1000000 ≤ log ((2:ℝ)/1) ∧ log ((2:ℝ)/1) ≤ (173287:ℝ)/250000 := by
  apply log_interval_of_atanh ((2:ℝ)/1) (by norm_num) 24
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_9_4_bounds : (81093:ℝ)/100000 ≤ log ((9:ℝ)/4) ∧ log ((9:ℝ)/4) ≤ (810931:ℝ)/1000000 := by
  apply log_interval_of_atanh ((9:ℝ)/4) (by norm_num) 24
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_5_2_bounds : (91629:ℝ)/100000 ≤ log ((5:ℝ)/2) ∧ log ((5:ℝ)/2) ≤ (916291:ℝ)/1000000 := by
  apply log_interval_of_atanh ((5:ℝ)/2) (by norm_num) 24
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_3_1_bounds : (274653:ℝ)/250000 ≤ log ((3:ℝ)/1) ∧ log ((3:ℝ)/1) ≤ (1098613:ℝ)/1000000 := by
  apply log_interval_of_atanh ((3:ℝ)/1) (by norm_num) 24
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_4_1_bounds : (693147:ℝ)/500000 ≤ log ((4:ℝ)/1) ∧ log ((4:ℝ)/1) ≤ (277259:ℝ)/200000 := by
  apply log_interval_of_atanh ((4:ℝ)/1) (by norm_num) 24
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_5_1_bounds : (1609437:ℝ)/1000000 ≤ log ((5:ℝ)/1) ∧ log ((5:ℝ)/1) ≤ (804719:ℝ)/500000 := by
  apply log_interval_of_atanh ((5:ℝ)/1) (by norm_num) 48
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_16_3_bounds : (209247:ℝ)/125000 ≤ log ((16:ℝ)/3) ∧ log ((16:ℝ)/3) ≤ (1673977:ℝ)/1000000 := by
  apply log_interval_of_atanh ((16:ℝ)/3) (by norm_num) 48
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_6_1_bounds : (1791759:ℝ)/1000000 ≤ log ((6:ℝ)/1) ∧ log ((6:ℝ)/1) ≤ (22397:ℝ)/12500 := by
  apply log_interval_of_atanh ((6:ℝ)/1) (by norm_num) 48
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_25_4_bounds : (1832581:ℝ)/1000000 ≤ log ((25:ℝ)/4) ∧ log ((25:ℝ)/4) ≤ (916291:ℝ)/500000 := by
  apply log_interval_of_atanh ((25:ℝ)/4) (by norm_num) 48
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_36_5_bounds : (1974081:ℝ)/1000000 ≤ log ((36:ℝ)/5) ∧ log ((36:ℝ)/5) ≤ (987041:ℝ)/500000 := by
  apply log_interval_of_atanh ((36:ℝ)/5) (by norm_num) 48
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

end SparseComponent.TotalFamily.Certificates
