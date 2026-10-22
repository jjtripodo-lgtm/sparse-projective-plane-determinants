import SparseComponent.TotalFamily.Density8.LogBounds
import SparseComponent.TotalFamily.PolynomialTools
import SparseComponent.TotalFamily.LogCertificates

namespace SparseComponent.TotalFamily.Density13
open Finset Matrix Real TotalOnes

set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

theorem log_two_precise : ((693147180559:ℝ)/1000000000000) ≤ log (2:ℝ) ∧ log (2:ℝ) ≤ ((8664339757:ℝ)/12500000000) := by
  exact Density8.log_two_precise

theorem log_14_13 : ((7410797:ℝ)/100000000) ≤ log ((14:ℝ)/13) ∧ log ((14:ℝ)/13) ≤ ((3705399:ℝ)/50000000) := by
  apply log_interval_of_atanh ((14:ℝ)/13) (by norm_num) 5
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_13_12 : ((800427:ℝ)/10000000) ≤ log ((13:ℝ)/12) ∧ log ((13:ℝ)/12) ≤ ((8004271:ℝ)/100000000) := by
  apply log_interval_of_atanh ((13:ℝ)/12) (by norm_num) 5
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_15_13 : ((3577521:ℝ)/25000000) ≤ log ((15:ℝ)/13) ∧ log ((15:ℝ)/13) ≤ ((2862017:ℝ)/20000000) := by
  apply log_interval_of_atanh ((15:ℝ)/13) (by norm_num) 6
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_13_11 : ((130511:ℝ)/781250) ≤ log ((13:ℝ)/11) ∧ log ((13:ℝ)/11) ≤ ((16705409:ℝ)/100000000) := by
  apply log_interval_of_atanh ((13:ℝ)/11) (by norm_num) 6
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_16_13 : ((648873:ℝ)/3125000) ≤ log ((16:ℝ)/13) ∧ log ((16:ℝ)/13) ≤ ((20763937:ℝ)/100000000) := by
  apply log_interval_of_atanh ((16:ℝ)/13) (by norm_num) 6
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_13_10 : ((13118213:ℝ)/50000000) ≤ log ((13:ℝ)/10) ∧ log ((13:ℝ)/10) ≤ ((26236427:ℝ)/100000000) := by
  apply log_interval_of_atanh ((13:ℝ)/10) (by norm_num) 7
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_17_13 : ((13413199:ℝ)/50000000) ≤ log ((17:ℝ)/13) ∧ log ((17:ℝ)/13) ≤ ((26826399:ℝ)/100000000) := by
  apply log_interval_of_atanh ((17:ℝ)/13) (by norm_num) 7
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_18_13 : ((203389:ℝ)/625000) ≤ log ((18:ℝ)/13) ∧ log ((18:ℝ)/13) ≤ ((32542241:ℝ)/100000000) := by
  apply log_interval_of_atanh ((18:ℝ)/13) (by norm_num) 7
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_13_9 : ((18386239:ℝ)/50000000) ≤ log ((13:ℝ)/9) ∧ log ((13:ℝ)/9) ≤ ((36772479:ℝ)/100000000) := by
  apply log_interval_of_atanh ((13:ℝ)/9) (by norm_num) 8
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_19_13 : ((18974481:ℝ)/50000000) ≤ log ((19:ℝ)/13) ∧ log ((19:ℝ)/13) ≤ ((37948963:ℝ)/100000000) := by
  apply log_interval_of_atanh ((19:ℝ)/13) (by norm_num) 8
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_20_13 : ((43078291:ℝ)/100000000) ≤ log ((20:ℝ)/13) ∧ log ((20:ℝ)/13) ≤ ((10769573:ℝ)/25000000) := by
  apply log_interval_of_atanh ((20:ℝ)/13) (by norm_num) 8
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_21_13 : ((11989327:ℝ)/25000000) ≤ log ((21:ℝ)/13) ∧ log ((21:ℝ)/13) ≤ ((47957309:ℝ)/100000000) := by
  apply log_interval_of_atanh ((21:ℝ)/13) (by norm_num) 9
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_13_8 : ((48550781:ℝ)/100000000) ≤ log ((13:ℝ)/8) ∧ log ((13:ℝ)/8) ≤ ((24275391:ℝ)/50000000) := by
  apply log_interval_of_atanh ((13:ℝ)/8) (by norm_num) 9
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_22_13 : ((52609309:ℝ)/100000000) ≤ log ((22:ℝ)/13) ∧ log ((22:ℝ)/13) ≤ ((5260931:ℝ)/10000000) := by
  apply log_interval_of_atanh ((22:ℝ)/13) (by norm_num) 9
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_23_13 : ((11410897:ℝ)/20000000) ≤ log ((23:ℝ)/13) ∧ log ((23:ℝ)/13) ≤ ((28527243:ℝ)/50000000) := by
  apply log_interval_of_atanh ((23:ℝ)/13) (by norm_num) 10
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_24_13 : ((61310447:ℝ)/100000000) ≤ log ((24:ℝ)/13) ∧ log ((24:ℝ)/13) ≤ ((3831903:ℝ)/6250000) := by
  apply log_interval_of_atanh ((24:ℝ)/13) (by norm_num) 10
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_13_7 : ((773799:ℝ)/1250000) ≤ log ((13:ℝ)/7) ∧ log ((13:ℝ)/7) ≤ ((61903921:ℝ)/100000000) := by
  apply log_interval_of_atanh ((13:ℝ)/7) (by norm_num) 11
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_25_13 : ((32696323:ℝ)/50000000) ≤ log ((25:ℝ)/13) ∧ log ((25:ℝ)/13) ≤ ((65392647:ℝ)/100000000) := by
  apply log_interval_of_atanh ((25:ℝ)/13) (by norm_num) 11
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_2_1 : ((34657359:ℝ)/50000000) ≤ log ((2:ℝ)/1) ∧ log ((2:ℝ)/1) ≤ ((69314719:ℝ)/100000000) := by
  apply log_interval_of_atanh ((2:ℝ)/1) (by norm_num) 11
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_27_13 : ((58471:ℝ)/80000) ≤ log ((27:ℝ)/13) ∧ log ((27:ℝ)/13) ≤ ((73088751:ℝ)/100000000) := by
  have hs : ((18870163991:ℝ)/500000000000) ≤ log ((27:ℝ)/26) ∧ log ((27:ℝ)/26) ≤ ((37740327983:ℝ)/1000000000000) := by
    apply log_interval_of_atanh ((27:ℝ)/26) (by norm_num) 6
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have he : log ((27:ℝ)/13) = log ((27:ℝ)/26)+1*log (2:ℝ) := by
    rw [show ((27:ℝ)/13) = ((27:ℝ)/26)*(2:ℝ)^1 by norm_num, log_mul (by norm_num) (by norm_num), log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hs.1, hs.2, log_two_precise.1, log_two_precise.2]

theorem log_28_13 : ((15345103:ℝ)/20000000) ≤ log ((28:ℝ)/13) ∧ log ((28:ℝ)/13) ≤ ((19181379:ℝ)/25000000) := by
  have hs : ((74107972153:ℝ)/1000000000000) ≤ log ((14:ℝ)/13) ∧ log ((14:ℝ)/13) ≤ ((37053986077:ℝ)/500000000000) := by
    apply log_interval_of_atanh ((14:ℝ)/13) (by norm_num) 6
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have he : log ((28:ℝ)/13) = log ((14:ℝ)/13)+1*log (2:ℝ) := by
    rw [show ((28:ℝ)/13) = ((14:ℝ)/13)*(2:ℝ)^1 by norm_num, log_mul (by norm_num) (by norm_num), log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hs.1, hs.2, log_two_precise.1, log_two_precise.2]

theorem log_13_6 : ((19329747:ℝ)/25000000) ≤ log ((13:ℝ)/6) ∧ log ((13:ℝ)/6) ≤ ((77318989:ℝ)/100000000) := by
  have hs : ((80042707673:ℝ)/1000000000000) ≤ log ((13:ℝ)/12) ∧ log ((13:ℝ)/12) ≤ ((40021353837:ℝ)/500000000000) := by
    apply log_interval_of_atanh ((13:ℝ)/12) (by norm_num) 7
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have he : log ((13:ℝ)/6) = log ((13:ℝ)/12)+1*log (2:ℝ) := by
    rw [show ((13:ℝ)/6) = ((13:ℝ)/12)*(2:ℝ)^1 by norm_num, log_mul (by norm_num) (by norm_num), log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hs.1, hs.2, log_two_precise.1, log_two_precise.2]

theorem log_29_13 : ((80234647:ℝ)/100000000) ≤ log ((29:ℝ)/13) ∧ log ((29:ℝ)/13) ≤ ((10029331:ℝ)/12500000) := by
  have hs : ((27299822991:ℝ)/250000000000) ≤ log ((29:ℝ)/26) ∧ log ((29:ℝ)/26) ≤ ((21839858393:ℝ)/200000000000) := by
    apply log_interval_of_atanh ((29:ℝ)/26) (by norm_num) 8
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have he : log ((29:ℝ)/13) = log ((29:ℝ)/26)+1*log (2:ℝ) := by
    rw [show ((29:ℝ)/13) = ((29:ℝ)/26)*(2:ℝ)^1 by norm_num, log_mul (by norm_num) (by norm_num), log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hs.1, hs.2, log_two_precise.1, log_two_precise.2]

theorem log_30_13 : ((41812401:ℝ)/50000000) ≤ log ((30:ℝ)/13) ∧ log ((30:ℝ)/13) ≤ ((83624803:ℝ)/100000000) := by
  have hs : ((3577521091:ℝ)/25000000000) ≤ log ((15:ℝ)/13) ∧ log ((15:ℝ)/13) ≤ ((143100843641:ℝ)/1000000000000) := by
    apply log_interval_of_atanh ((15:ℝ)/13) (by norm_num) 8
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have he : log ((30:ℝ)/13) = log ((15:ℝ)/13)+1*log (2:ℝ) := by
    rw [show ((30:ℝ)/13) = ((15:ℝ)/13)*(2:ℝ)^1 by norm_num, log_mul (by norm_num) (by norm_num), log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hs.1, hs.2, log_two_precise.1, log_two_precise.2]

theorem log_31_13 : ((10862973:ℝ)/12500000) ≤ log ((31:ℝ)/13) ∧ log ((31:ℝ)/13) ≤ ((17380757:ℝ)/20000000) := by
  have hs : ((175890666463:ℝ)/1000000000000) ≤ log ((31:ℝ)/26) ∧ log ((31:ℝ)/26) ≤ ((5496583327:ℝ)/31250000000) := by
    apply log_interval_of_atanh ((31:ℝ)/26) (by norm_num) 8
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have he : log ((31:ℝ)/13) = log ((31:ℝ)/26)+1*log (2:ℝ) := by
    rw [show ((31:ℝ)/13) = ((31:ℝ)/26)*(2:ℝ)^1 by norm_num, log_mul (by norm_num) (by norm_num), log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hs.1, hs.2, log_two_precise.1, log_two_precise.2]

theorem log_32_13 : ((45039327:ℝ)/50000000) ≤ log ((32:ℝ)/13) ∧ log ((32:ℝ)/13) ≤ ((18015731:ℝ)/20000000) := by
  have hs : ((103819682389:ℝ)/500000000000) ≤ log ((16:ℝ)/13) ∧ log ((16:ℝ)/13) ≤ ((207639364779:ℝ)/1000000000000) := by
    apply log_interval_of_atanh ((16:ℝ)/13) (by norm_num) 8
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have he : log ((32:ℝ)/13) = log ((16:ℝ)/13)+1*log (2:ℝ) := by
    rw [show ((32:ℝ)/13) = ((16:ℝ)/13)*(2:ℝ)^1 by norm_num, log_mul (by norm_num) (by norm_num), log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hs.1, hs.2, log_two_precise.1, log_two_precise.2]

theorem log_33_13 : ((4657791:ℝ)/5000000) ≤ log ((33:ℝ)/13) ∧ log ((33:ℝ)/13) ≤ ((93155821:ℝ)/100000000) := by
  have hs : ((59602755861:ℝ)/250000000000) ≤ log ((33:ℝ)/26) ∧ log ((33:ℝ)/26) ≤ ((47682204689:ℝ)/200000000000) := by
    apply log_interval_of_atanh ((33:ℝ)/26) (by norm_num) 10
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have he : log ((33:ℝ)/13) = log ((33:ℝ)/26)+1*log (2:ℝ) := by
    rw [show ((33:ℝ)/13) = ((33:ℝ)/26)*(2:ℝ)^1 by norm_num, log_mul (by norm_num) (by norm_num), log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hs.1, hs.2, log_two_precise.1, log_two_precise.2]

theorem log_13_5 : ((11943893:ℝ)/12500000) ≤ log ((13:ℝ)/5) ∧ log ((13:ℝ)/5) ≤ ((19110229:ℝ)/20000000) := by
  have hs : ((262364264467:ℝ)/1000000000000) ≤ log ((13:ℝ)/10) ∧ log ((13:ℝ)/10) ≤ ((65591066117:ℝ)/250000000000) := by
    apply log_interval_of_atanh ((13:ℝ)/10) (by norm_num) 9
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have he : log ((13:ℝ)/5) = log ((13:ℝ)/10)+1*log (2:ℝ) := by
    rw [show ((13:ℝ)/5) = ((13:ℝ)/10)*(2:ℝ)^1 by norm_num, log_mul (by norm_num) (by norm_num), log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hs.1, hs.2, log_two_precise.1, log_two_precise.2]

theorem log_34_13 : ((24035279:ℝ)/25000000) ≤ log ((34:ℝ)/13) ∧ log ((34:ℝ)/13) ≤ ((96141117:ℝ)/100000000) := by
  have hs : ((134131993297:ℝ)/500000000000) ≤ log ((17:ℝ)/13) ∧ log ((17:ℝ)/13) ≤ ((53652797319:ℝ)/200000000000) := by
    apply log_interval_of_atanh ((17:ℝ)/13) (by norm_num) 9
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have he : log ((34:ℝ)/13) = log ((17:ℝ)/13)+1*log (2:ℝ) := by
    rw [show ((34:ℝ)/13) = ((17:ℝ)/13)*(2:ℝ)^1 by norm_num, log_mul (by norm_num) (by norm_num), log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hs.1, hs.2, log_two_precise.1, log_two_precise.2]

theorem log_35_13 : ((9903987:ℝ)/10000000) ≤ log ((35:ℝ)/13) ∧ log ((35:ℝ)/13) ≤ ((99039871:ℝ)/100000000) := by
  have hs : ((297251523467:ℝ)/1000000000000) ≤ log ((35:ℝ)/26) ∧ log ((35:ℝ)/26) ≤ ((74312880867:ℝ)/250000000000) := by
    apply log_interval_of_atanh ((35:ℝ)/26) (by norm_num) 10
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have he : log ((35:ℝ)/13) = log ((35:ℝ)/26)+1*log (2:ℝ) := by
    rw [show ((35:ℝ)/13) = ((35:ℝ)/26)*(2:ℝ)^1 by norm_num, log_mul (by norm_num) (by norm_num), log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hs.1, hs.2, log_two_precise.1, log_two_precise.2]

theorem log_36_13 : ((50928479:ℝ)/50000000) ≤ log ((36:ℝ)/13) ∧ log ((36:ℝ)/13) ≤ ((101856959:ℝ)/100000000) := by
  have hs : ((162711200217:ℝ)/500000000000) ≤ log ((18:ℝ)/13) ∧ log ((18:ℝ)/13) ≤ ((65084480087:ℝ)/200000000000) := by
    apply log_interval_of_atanh ((18:ℝ)/13) (by norm_num) 10
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have he : log ((36:ℝ)/13) = log ((18:ℝ)/13)+1*log (2:ℝ) := by
    rw [show ((36:ℝ)/13) = ((18:ℝ)/13)*(2:ℝ)^1 by norm_num, log_mul (by norm_num) (by norm_num), log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hs.1, hs.2, log_two_precise.1, log_two_precise.2]

theorem log_37_13 : ((20919371:ℝ)/20000000) ≤ log ((37:ℝ)/13) ∧ log ((37:ℝ)/13) ≤ ((13074607:ℝ)/12500000) := by
  have hs : ((176410687311:ℝ)/500000000000) ≤ log ((37:ℝ)/26) ∧ log ((37:ℝ)/26) ≤ ((352821374623:ℝ)/1000000000000) := by
    apply log_interval_of_atanh ((37:ℝ)/26) (by norm_num) 10
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have he : log ((37:ℝ)/13) = log ((37:ℝ)/26)+1*log (2:ℝ) := by
    rw [show ((37:ℝ)/13) = ((37:ℝ)/26)*(2:ℝ)^1 by norm_num, log_mul (by norm_num) (by norm_num), log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hs.1, hs.2, log_two_precise.1, log_two_precise.2]

theorem log_38_13 : ((335199:ℝ)/312500) ≤ log ((38:ℝ)/13) ∧ log ((38:ℝ)/13) ≤ ((107263681:ℝ)/100000000) := by
  have hs : ((47436202713:ℝ)/125000000000) ≤ log ((19:ℝ)/13) ∧ log ((19:ℝ)/13) ≤ ((75897924341:ℝ)/200000000000) := by
    apply log_interval_of_atanh ((19:ℝ)/13) (by norm_num) 11
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have he : log ((38:ℝ)/13) = log ((19:ℝ)/13)+1*log (2:ℝ) := by
    rw [show ((38:ℝ)/13) = ((19:ℝ)/13)*(2:ℝ)^1 by norm_num, log_mul (by norm_num) (by norm_num), log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hs.1, hs.2, log_two_precise.1, log_two_precise.2]

theorem log_3_1 : ((27465307:ℝ)/25000000) ≤ log ((3:ℝ)/1) ∧ log ((3:ℝ)/1) ≤ ((109861229:ℝ)/100000000) := by
  have hs : ((101366277027:ℝ)/250000000000) ≤ log ((3:ℝ)/2) ∧ log ((3:ℝ)/2) ≤ ((405465108109:ℝ)/1000000000000) := by
    apply log_interval_of_atanh ((3:ℝ)/2) (by norm_num) 11
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have he : log ((3:ℝ)/1) = log ((3:ℝ)/2)+1*log (2:ℝ) := by
    rw [show ((3:ℝ)/1) = ((3:ℝ)/2)*(2:ℝ)^1 by norm_num, log_mul (by norm_num) (by norm_num), log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hs.1, hs.2, log_two_precise.1, log_two_precise.2]

theorem log_40_13 : ((112393009:ℝ)/100000000) ≤ log ((40:ℝ)/13) ∧ log ((40:ℝ)/13) ≤ ((11239301:ℝ)/10000000) := by
  have hs : ((107695729023:ℝ)/250000000000) ≤ log ((20:ℝ)/13) ∧ log ((20:ℝ)/13) ≤ ((430782916093:ℝ)/1000000000000) := by
    apply log_interval_of_atanh ((20:ℝ)/13) (by norm_num) 11
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have he : log ((40:ℝ)/13) = log ((20:ℝ)/13)+1*log (2:ℝ) := by
    rw [show ((40:ℝ)/13) = ((20:ℝ)/13)*(2:ℝ)^1 by norm_num, log_mul (by norm_num) (by norm_num), log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hs.1, hs.2, log_two_precise.1, log_two_precise.2]

theorem log_13_4 : ((117865499:ℝ)/100000000) ≤ log ((13:ℝ)/4) ∧ log ((13:ℝ)/4) ≤ ((235731:ℝ)/200000) := by
  have hs : ((485507815781:ℝ)/1000000000000) ≤ log ((13:ℝ)/8) ∧ log ((13:ℝ)/8) ≤ ((242753907891:ℝ)/500000000000) := by
    apply log_interval_of_atanh ((13:ℝ)/8) (by norm_num) 12
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have he : log ((13:ℝ)/4) = log ((13:ℝ)/8)+1*log (2:ℝ) := by
    rw [show ((13:ℝ)/4) = ((13:ℝ)/8)*(2:ℝ)^1 by norm_num, log_mul (by norm_num) (by norm_num), log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hs.1, hs.2, log_two_precise.1, log_two_precise.2]

theorem log_13_3 : ((73316853:ℝ)/50000000) ≤ log ((13:ℝ)/3) ∧ log ((13:ℝ)/3) ≤ ((146633707:ℝ)/100000000) := by
  have hs : ((80042707673:ℝ)/1000000000000) ≤ log ((13:ℝ)/12) ∧ log ((13:ℝ)/12) ≤ ((40021353837:ℝ)/500000000000) := by
    apply log_interval_of_atanh ((13:ℝ)/12) (by norm_num) 7
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have he : log ((13:ℝ)/3) = log ((13:ℝ)/12)+2*log (2:ℝ) := by
    rw [show ((13:ℝ)/3) = ((13:ℝ)/12)*(2:ℝ)^2 by norm_num, log_mul (by norm_num) (by norm_num), log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hs.1, hs.2, log_two_precise.1, log_two_precise.2]

theorem log_12_1 : ((31061333:ℝ)/12500000) ≤ log ((12:ℝ)/1) ∧ log ((12:ℝ)/1) ≤ ((49698133:ℝ)/20000000) := by
  have hs : ((101366277027:ℝ)/250000000000) ≤ log ((3:ℝ)/2) ∧ log ((3:ℝ)/2) ≤ ((405465108109:ℝ)/1000000000000) := by
    apply log_interval_of_atanh ((3:ℝ)/2) (by norm_num) 11
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have he : log ((12:ℝ)/1) = log ((3:ℝ)/2)+3*log (2:ℝ) := by
    rw [show ((12:ℝ)/1) = ((3:ℝ)/2)*(2:ℝ)^3 by norm_num, log_mul (by norm_num) (by norm_num), log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hs.1, hs.2, log_two_precise.1, log_two_precise.2]

theorem log_13_1 : ((51298987:ℝ)/20000000) ≤ log ((13:ℝ)/1) ∧ log ((13:ℝ)/1) ≤ ((32061867:ℝ)/12500000) := by
  have hs : ((485507815781:ℝ)/1000000000000) ≤ log ((13:ℝ)/8) ∧ log ((13:ℝ)/8) ≤ ((242753907891:ℝ)/500000000000) := by
    apply log_interval_of_atanh ((13:ℝ)/8) (by norm_num) 12
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have he : log ((13:ℝ)/1) = log ((13:ℝ)/8)+3*log (2:ℝ) := by
    rw [show ((13:ℝ)/1) = ((13:ℝ)/8)*(2:ℝ)^3 by norm_num, log_mul (by norm_num) (by norm_num), log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hs.1, hs.2, log_two_precise.1, log_two_precise.2]

theorem log_169_12 : ((132249603:ℝ)/50000000) ≤ log ((169:ℝ)/12) ∧ log ((169:ℝ)/12) ≤ ((264499207:ℝ)/100000000) := by
  have hs : ((113110104691:ℝ)/200000000000) ≤ log ((169:ℝ)/96) ∧ log ((169:ℝ)/96) ≤ ((8836726929:ℝ)/15625000000) := by
    apply log_interval_of_atanh ((169:ℝ)/96) (by norm_num) 13
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have he : log ((169:ℝ)/12) = log ((169:ℝ)/96)+3*log (2:ℝ) := by
    rw [show ((169:ℝ)/12) = ((169:ℝ)/96)*(2:ℝ)^3 by norm_num, log_mul (by norm_num) (by norm_num), log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hs.1, hs.2, log_two_precise.1, log_two_precise.2]

theorem gamma_bounds : ((42347929:ℝ)/100000000000) ≤ gamma 13 ∧ gamma 13 ≤ ((42347931:ℝ)/100000000000) := by
  have h := log_169_12
  unfold gamma logGamma
  rw [← log_div (by norm_num : (13:ℝ)^2 ≠ 0) (by norm_num : (13:ℝ)-1 ≠ 0)]
  norm_num at h ⊢
  constructor <;> linarith

theorem ratio_log_lower_3 : ((73316853:ℝ)/50000000) ≤ log ((13:ℝ)/3) := by
  convert log_13_3.1 using 1 <;> norm_num

theorem ratio_log_lower_4 : ((117865499:ℝ)/100000000) ≤ log ((13:ℝ)/4) := by
  convert log_13_4.1 using 1 <;> norm_num

theorem ratio_log_lower_5 : ((11943893:ℝ)/12500000) ≤ log ((13:ℝ)/5) := by
  convert log_13_5.1 using 1 <;> norm_num

theorem ratio_log_lower_6 : ((19329747:ℝ)/25000000) ≤ log ((13:ℝ)/6) := by
  convert log_13_6.1 using 1 <;> norm_num

theorem ratio_log_lower_7 : ((773799:ℝ)/1250000) ≤ log ((13:ℝ)/7) := by
  convert log_13_7.1 using 1 <;> norm_num

theorem ratio_log_lower_8 : ((48550781:ℝ)/100000000) ≤ log ((13:ℝ)/8) := by
  convert log_13_8.1 using 1 <;> norm_num

theorem ratio_log_lower_9 : ((18386239:ℝ)/50000000) ≤ log ((13:ℝ)/9) := by
  convert log_13_9.1 using 1 <;> norm_num

theorem ratio_log_lower_10 : ((13118213:ℝ)/50000000) ≤ log ((13:ℝ)/10) := by
  convert log_13_10.1 using 1 <;> norm_num

theorem ratio_log_lower_11 : ((130511:ℝ)/781250) ≤ log ((13:ℝ)/11) := by
  convert log_13_11.1 using 1 <;> norm_num

theorem ratio_log_lower_12 : ((800427:ℝ)/10000000) ≤ log ((13:ℝ)/12) := by
  convert log_13_12.1 using 1 <;> norm_num

theorem ratio_log_lower_13 : ((0:ℝ)/1) ≤ log ((13:ℝ)/13) := by
  norm_num

theorem ratio_log_lower_14 : ((-3705399:ℝ)/50000000) ≤ log ((13:ℝ)/14) := by
  rw [show (13:ℝ)/14 = (((14:ℝ)/13))⁻¹ by norm_num, log_inv]
  linarith [log_14_13.2]

theorem ratio_log_lower_15 : ((-2862017:ℝ)/20000000) ≤ log ((13:ℝ)/15) := by
  rw [show (13:ℝ)/15 = (((15:ℝ)/13))⁻¹ by norm_num, log_inv]
  linarith [log_15_13.2]

theorem ratio_log_lower_16 : ((-20763937:ℝ)/100000000) ≤ log ((13:ℝ)/16) := by
  rw [show (13:ℝ)/16 = (((16:ℝ)/13))⁻¹ by norm_num, log_inv]
  linarith [log_16_13.2]

theorem ratio_log_lower_17 : ((-26826399:ℝ)/100000000) ≤ log ((13:ℝ)/17) := by
  rw [show (13:ℝ)/17 = (((17:ℝ)/13))⁻¹ by norm_num, log_inv]
  linarith [log_17_13.2]

theorem ratio_log_lower_18 : ((-32542241:ℝ)/100000000) ≤ log ((13:ℝ)/18) := by
  rw [show (13:ℝ)/18 = (((18:ℝ)/13))⁻¹ by norm_num, log_inv]
  linarith [log_18_13.2]

theorem ratio_log_lower_19 : ((-37948963:ℝ)/100000000) ≤ log ((13:ℝ)/19) := by
  rw [show (13:ℝ)/19 = (((19:ℝ)/13))⁻¹ by norm_num, log_inv]
  linarith [log_19_13.2]

theorem ratio_log_lower_20 : ((-10769573:ℝ)/25000000) ≤ log ((13:ℝ)/20) := by
  rw [show (13:ℝ)/20 = (((20:ℝ)/13))⁻¹ by norm_num, log_inv]
  linarith [log_20_13.2]

theorem ratio_log_lower_21 : ((-47957309:ℝ)/100000000) ≤ log ((13:ℝ)/21) := by
  rw [show (13:ℝ)/21 = (((21:ℝ)/13))⁻¹ by norm_num, log_inv]
  linarith [log_21_13.2]

theorem ratio_log_lower_22 : ((-5260931:ℝ)/10000000) ≤ log ((13:ℝ)/22) := by
  rw [show (13:ℝ)/22 = (((22:ℝ)/13))⁻¹ by norm_num, log_inv]
  linarith [log_22_13.2]

theorem ratio_log_lower_23 : ((-28527243:ℝ)/50000000) ≤ log ((13:ℝ)/23) := by
  rw [show (13:ℝ)/23 = (((23:ℝ)/13))⁻¹ by norm_num, log_inv]
  linarith [log_23_13.2]

theorem ratio_log_lower_24 : ((-3831903:ℝ)/6250000) ≤ log ((13:ℝ)/24) := by
  rw [show (13:ℝ)/24 = (((24:ℝ)/13))⁻¹ by norm_num, log_inv]
  linarith [log_24_13.2]

theorem ratio_log_lower_25 : ((-65392647:ℝ)/100000000) ≤ log ((13:ℝ)/25) := by
  rw [show (13:ℝ)/25 = (((25:ℝ)/13))⁻¹ by norm_num, log_inv]
  linarith [log_25_13.2]

theorem ratio_log_lower_26 : ((-69314719:ℝ)/100000000) ≤ log ((13:ℝ)/26) := by
  rw [show (13:ℝ)/26 = (((2:ℝ)/1))⁻¹ by norm_num, log_inv]
  linarith [log_2_1.2]

theorem ratio_log_lower_27 : ((-73088751:ℝ)/100000000) ≤ log ((13:ℝ)/27) := by
  rw [show (13:ℝ)/27 = (((27:ℝ)/13))⁻¹ by norm_num, log_inv]
  linarith [log_27_13.2]

theorem ratio_log_lower_28 : ((-19181379:ℝ)/25000000) ≤ log ((13:ℝ)/28) := by
  rw [show (13:ℝ)/28 = (((28:ℝ)/13))⁻¹ by norm_num, log_inv]
  linarith [log_28_13.2]

theorem ratio_log_lower_29 : ((-10029331:ℝ)/12500000) ≤ log ((13:ℝ)/29) := by
  rw [show (13:ℝ)/29 = (((29:ℝ)/13))⁻¹ by norm_num, log_inv]
  linarith [log_29_13.2]

theorem ratio_log_lower_30 : ((-83624803:ℝ)/100000000) ≤ log ((13:ℝ)/30) := by
  rw [show (13:ℝ)/30 = (((30:ℝ)/13))⁻¹ by norm_num, log_inv]
  linarith [log_30_13.2]

theorem ratio_log_lower_31 : ((-17380757:ℝ)/20000000) ≤ log ((13:ℝ)/31) := by
  rw [show (13:ℝ)/31 = (((31:ℝ)/13))⁻¹ by norm_num, log_inv]
  linarith [log_31_13.2]

theorem ratio_log_lower_32 : ((-18015731:ℝ)/20000000) ≤ log ((13:ℝ)/32) := by
  rw [show (13:ℝ)/32 = (((32:ℝ)/13))⁻¹ by norm_num, log_inv]
  linarith [log_32_13.2]

theorem ratio_log_lower_33 : ((-93155821:ℝ)/100000000) ≤ log ((13:ℝ)/33) := by
  rw [show (13:ℝ)/33 = (((33:ℝ)/13))⁻¹ by norm_num, log_inv]
  linarith [log_33_13.2]

theorem ratio_log_lower_34 : ((-96141117:ℝ)/100000000) ≤ log ((13:ℝ)/34) := by
  rw [show (13:ℝ)/34 = (((34:ℝ)/13))⁻¹ by norm_num, log_inv]
  linarith [log_34_13.2]

theorem ratio_log_lower_35 : ((-99039871:ℝ)/100000000) ≤ log ((13:ℝ)/35) := by
  rw [show (13:ℝ)/35 = (((35:ℝ)/13))⁻¹ by norm_num, log_inv]
  linarith [log_35_13.2]

theorem ratio_log_lower_36 : ((-101856959:ℝ)/100000000) ≤ log ((13:ℝ)/36) := by
  rw [show (13:ℝ)/36 = (((36:ℝ)/13))⁻¹ by norm_num, log_inv]
  linarith [log_36_13.2]

theorem ratio_log_lower_37 : ((-13074607:ℝ)/12500000) ≤ log ((13:ℝ)/37) := by
  rw [show (13:ℝ)/37 = (((37:ℝ)/13))⁻¹ by norm_num, log_inv]
  linarith [log_37_13.2]

theorem ratio_log_lower_38 : ((-107263681:ℝ)/100000000) ≤ log ((13:ℝ)/38) := by
  rw [show (13:ℝ)/38 = (((38:ℝ)/13))⁻¹ by norm_num, log_inv]
  linarith [log_38_13.2]

theorem ratio_log_lower_39 : ((-109861229:ℝ)/100000000) ≤ log ((13:ℝ)/39) := by
  rw [show (13:ℝ)/39 = (((3:ℝ)/1))⁻¹ by norm_num, log_inv]
  linarith [log_3_1.2]

theorem ratio_log_lower_40 : ((-11239301:ℝ)/10000000) ≤ log ((13:ℝ)/40) := by
  rw [show (13:ℝ)/40 = (((40:ℝ)/13))⁻¹ by norm_num, log_inv]
  linarith [log_40_13.2]

end SparseComponent.TotalFamily.Density13
