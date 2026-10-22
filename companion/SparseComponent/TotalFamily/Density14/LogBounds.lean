import SparseComponent.TotalFamily.Density8.LogBounds
import SparseComponent.TotalFamily.PolynomialTools
import SparseComponent.TotalFamily.LogCertificates

namespace SparseComponent.TotalFamily.Density14
open Finset Matrix Real TotalOnes

set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

theorem log_two_precise : ((693147180559:ℝ)/1000000000000) ≤ log (2:ℝ) ∧ log (2:ℝ) ≤ ((8664339757:ℝ)/12500000000) := by
  exact Density8.log_two_precise

theorem log_15_14 : ((6899287:ℝ)/100000000) ≤ log ((15:ℝ)/14) ∧ log ((15:ℝ)/14) ≤ ((862411:ℝ)/12500000) := by
  apply log_interval_of_atanh ((15:ℝ)/14) (by norm_num) 5
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_14_13 : ((7410797:ℝ)/100000000) ≤ log ((14:ℝ)/13) ∧ log ((14:ℝ)/13) ≤ ((3705399:ℝ)/50000000) := by
  apply log_interval_of_atanh ((14:ℝ)/13) (by norm_num) 5
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_8_7 : ((13353139:ℝ)/100000000) ≤ log ((8:ℝ)/7) ∧ log ((8:ℝ)/7) ≤ ((667657:ℝ)/5000000) := by
  apply log_interval_of_atanh ((8:ℝ)/7) (by norm_num) 6
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_7_6 : ((15415067:ℝ)/100000000) ≤ log ((7:ℝ)/6) ∧ log ((7:ℝ)/6) ≤ ((3853767:ℝ)/25000000) := by
  apply log_interval_of_atanh ((7:ℝ)/6) (by norm_num) 6
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_17_14 : ((19415601:ℝ)/100000000) ≤ log ((17:ℝ)/14) ∧ log ((17:ℝ)/14) ≤ ((9707801:ℝ)/50000000) := by
  apply log_interval_of_atanh ((17:ℝ)/14) (by norm_num) 6
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_14_11 : ((4823241:ℝ)/20000000) ≤ log ((14:ℝ)/11) ∧ log ((14:ℝ)/11) ≤ ((12058103:ℝ)/50000000) := by
  apply log_interval_of_atanh ((14:ℝ)/11) (by norm_num) 7
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_9_7 : ((12565721:ℝ)/50000000) ≤ log ((9:ℝ)/7) ∧ log ((9:ℝ)/7) ≤ ((25131443:ℝ)/100000000) := by
  apply log_interval_of_atanh ((9:ℝ)/7) (by norm_num) 7
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_19_14 : ((7634541:ℝ)/25000000) ≤ log ((19:ℝ)/14) ∧ log ((19:ℝ)/14) ≤ ((6107633:ℝ)/20000000) := by
  apply log_interval_of_atanh ((19:ℝ)/14) (by norm_num) 8
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

theorem log_14_9 : ((1767331:ℝ)/4000000) ≤ log ((14:ℝ)/9) ∧ log ((14:ℝ)/9) ≤ ((11045819:ℝ)/25000000) := by
  apply log_interval_of_atanh ((14:ℝ)/9) (by norm_num) 8
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_11_7 : ((2824907:ℝ)/6250000) ≤ log ((11:ℝ)/7) ∧ log ((11:ℝ)/7) ≤ ((45198513:ℝ)/100000000) := by
  apply log_interval_of_atanh ((11:ℝ)/7) (by norm_num) 9
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_23_14 : ((6205461:ℝ)/12500000) ≤ log ((23:ℝ)/14) ∧ log ((23:ℝ)/14) ≤ ((49643689:ℝ)/100000000) := by
  apply log_interval_of_atanh ((23:ℝ)/14) (by norm_num) 9
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

theorem log_25_14 : ((57981849:ℝ)/100000000) ≤ log ((25:ℝ)/14) ∧ log ((25:ℝ)/14) ≤ ((1159637:ℝ)/2000000) := by
  apply log_interval_of_atanh ((25:ℝ)/14) (by norm_num) 10
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_13_7 : ((773799:ℝ)/1250000) ≤ log ((13:ℝ)/7) ∧ log ((13:ℝ)/7) ≤ ((61903921:ℝ)/100000000) := by
  apply log_interval_of_atanh ((13:ℝ)/7) (by norm_num) 11
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_27_14 : ((65677953:ℝ)/100000000) ≤ log ((27:ℝ)/14) ∧ log ((27:ℝ)/14) ≤ ((32838977:ℝ)/50000000) := by
  apply log_interval_of_atanh ((27:ℝ)/14) (by norm_num) 11
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_2_1 : ((34657359:ℝ)/50000000) ≤ log ((2:ℝ)/1) ∧ log ((2:ℝ)/1) ≤ ((69314719:ℝ)/100000000) := by
  apply log_interval_of_atanh ((2:ℝ)/1) (by norm_num) 11
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_29_14 : ((1456477:ℝ)/2000000) ≤ log ((29:ℝ)/14) ∧ log ((29:ℝ)/14) ≤ ((72823851:ℝ)/100000000) := by
  have hs : ((35091319811:ℝ)/1000000000000) ≤ log ((29:ℝ)/28) ∧ log ((29:ℝ)/28) ≤ ((8772829953:ℝ)/250000000000) := by
    apply log_interval_of_atanh ((29:ℝ)/28) (by norm_num) 6
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have he : log ((29:ℝ)/14) = log ((29:ℝ)/28)+1*log (2:ℝ) := by
    rw [show ((29:ℝ)/14) = ((29:ℝ)/28)*(2:ℝ)^1 by norm_num, log_mul (by norm_num) (by norm_num), log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hs.1, hs.2, log_two_precise.1, log_two_precise.2]

theorem log_15_7 : ((15242801:ℝ)/20000000) ≤ log ((15:ℝ)/7) ∧ log ((15:ℝ)/7) ≤ ((38107003:ℝ)/50000000) := by
  have hs : ((34496435743:ℝ)/500000000000) ≤ log ((15:ℝ)/14) ∧ log ((15:ℝ)/14) ≤ ((68992871487:ℝ)/1000000000000) := by
    apply log_interval_of_atanh ((15:ℝ)/14) (by norm_num) 7
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have he : log ((15:ℝ)/7) = log ((15:ℝ)/14)+1*log (2:ℝ) := by
    rw [show ((15:ℝ)/7) = ((15:ℝ)/14)*(2:ℝ)^1 by norm_num, log_mul (by norm_num) (by norm_num), log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hs.1, hs.2, log_two_precise.1, log_two_precise.2]

theorem log_31_14 : ((79492987:ℝ)/100000000) ≤ log ((31:ℝ)/14) ∧ log ((31:ℝ)/14) ≤ ((19873247:ℝ)/25000000) := by
  have hs : ((101782694309:ℝ)/1000000000000) ≤ log ((31:ℝ)/28) ∧ log ((31:ℝ)/28) ≤ ((10178269431:ℝ)/100000000000) := by
    apply log_interval_of_atanh ((31:ℝ)/28) (by norm_num) 7
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have he : log ((31:ℝ)/14) = log ((31:ℝ)/28)+1*log (2:ℝ) := by
    rw [show ((31:ℝ)/14) = ((31:ℝ)/28)*(2:ℝ)^1 by norm_num, log_mul (by norm_num) (by norm_num), log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hs.1, hs.2, log_two_precise.1, log_two_precise.2]

theorem log_16_7 : ((82667857:ℝ)/100000000) ≤ log ((16:ℝ)/7) ∧ log ((16:ℝ)/7) ≤ ((41333929:ℝ)/50000000) := by
  have hs : ((8345712039:ℝ)/62500000000) ≤ log ((8:ℝ)/7) ∧ log ((8:ℝ)/7) ≤ ((1068251141:ℝ)/8000000000) := by
    apply log_interval_of_atanh ((8:ℝ)/7) (by norm_num) 7
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have he : log ((16:ℝ)/7) = log ((8:ℝ)/7)+1*log (2:ℝ) := by
    rw [show ((16:ℝ)/7) = ((8:ℝ)/7)*(2:ℝ)^1 by norm_num, log_mul (by norm_num) (by norm_num), log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hs.1, hs.2, log_two_precise.1, log_two_precise.2]

theorem log_7_3 : ((42364893:ℝ)/50000000) ≤ log ((7:ℝ)/3) ∧ log ((7:ℝ)/3) ≤ ((84729787:ℝ)/100000000) := by
  have hs : ((154150679827:ℝ)/1000000000000) ≤ log ((7:ℝ)/6) ∧ log ((7:ℝ)/6) ≤ ((38537669957:ℝ)/250000000000) := by
    apply log_interval_of_atanh ((7:ℝ)/6) (by norm_num) 8
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have he : log ((7:ℝ)/3) = log ((7:ℝ)/6)+1*log (2:ℝ) := by
    rw [show ((7:ℝ)/3) = ((7:ℝ)/6)*(2:ℝ)^1 by norm_num, log_mul (by norm_num) (by norm_num), log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hs.1, hs.2, log_two_precise.1, log_two_precise.2]

theorem log_33_14 : ((85745023:ℝ)/100000000) ≤ log ((33:ℝ)/14) ∧ log ((33:ℝ)/14) ≤ ((669883:ℝ)/781250) := by
  have hs : ((164303051291:ℝ)/1000000000000) ≤ log ((33:ℝ)/28) ∧ log ((33:ℝ)/28) ≤ ((41075762823:ℝ)/250000000000) := by
    apply log_interval_of_atanh ((33:ℝ)/28) (by norm_num) 8
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have he : log ((33:ℝ)/14) = log ((33:ℝ)/28)+1*log (2:ℝ) := by
    rw [show ((33:ℝ)/14) = ((33:ℝ)/28)*(2:ℝ)^1 by norm_num, log_mul (by norm_num) (by norm_num), log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hs.1, hs.2, log_two_precise.1, log_two_precise.2]

theorem log_17_7 : ((88730319:ℝ)/100000000) ≤ log ((17:ℝ)/7) ∧ log ((17:ℝ)/7) ≤ ((1109129:ℝ)/1250000) := by
  have hs : ((4853900361:ℝ)/25000000000) ≤ log ((17:ℝ)/14) ∧ log ((17:ℝ)/14) ≤ ((194156014441:ℝ)/1000000000000) := by
    apply log_interval_of_atanh ((17:ℝ)/14) (by norm_num) 9
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have he : log ((17:ℝ)/7) = log ((17:ℝ)/14)+1*log (2:ℝ) := by
    rw [show ((17:ℝ)/7) = ((17:ℝ)/14)*(2:ℝ)^1 by norm_num, log_mul (by norm_num) (by norm_num), log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hs.1, hs.2, log_two_precise.1, log_two_precise.2]

theorem log_5_2 : ((91629073:ℝ)/100000000) ≤ log ((5:ℝ)/2) ∧ log ((5:ℝ)/2) ≤ ((45814537:ℝ)/50000000) := by
  have hs : ((111571775657:ℝ)/500000000000) ≤ log ((5:ℝ)/4) ∧ log ((5:ℝ)/4) ≤ ((44628710263:ℝ)/200000000000) := by
    apply log_interval_of_atanh ((5:ℝ)/4) (by norm_num) 8
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have he : log ((5:ℝ)/2) = log ((5:ℝ)/4)+1*log (2:ℝ) := by
    rw [show ((5:ℝ)/2) = ((5:ℝ)/4)*(2:ℝ)^1 by norm_num, log_mul (by norm_num) (by norm_num), log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hs.1, hs.2, log_two_precise.1, log_two_precise.2]

theorem log_18_7 : ((1180577:ℝ)/1250000) ≤ log ((18:ℝ)/7) ∧ log ((18:ℝ)/7) ≤ ((94446161:ℝ)/100000000) := by
  have hs : ((6282860707:ℝ)/25000000000) ≤ log ((9:ℝ)/7) ∧ log ((9:ℝ)/7) ≤ ((251314428281:ℝ)/1000000000000) := by
    apply log_interval_of_atanh ((9:ℝ)/7) (by norm_num) 9
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have he : log ((18:ℝ)/7) = log ((9:ℝ)/7)+1*log (2:ℝ) := by
    rw [show ((18:ℝ)/7) = ((9:ℝ)/7)*(2:ℝ)^1 by norm_num, log_mul (by norm_num) (by norm_num), log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hs.1, hs.2, log_two_precise.1, log_two_precise.2]

theorem log_37_14 : ((48593029:ℝ)/50000000) ≤ log ((37:ℝ)/14) ∧ log ((37:ℝ)/14) ≤ ((97186059:ℝ)/100000000) := by
  have hs : ((278713402469:ℝ)/1000000000000) ≤ log ((37:ℝ)/28) ∧ log ((37:ℝ)/28) ≤ ((27871340247:ℝ)/100000000000) := by
    apply log_interval_of_atanh ((37:ℝ)/28) (by norm_num) 9
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have he : log ((37:ℝ)/14) = log ((37:ℝ)/28)+1*log (2:ℝ) := by
    rw [show ((37:ℝ)/14) = ((37:ℝ)/28)*(2:ℝ)^1 by norm_num, log_mul (by norm_num) (by norm_num), log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hs.1, hs.2, log_two_precise.1, log_two_precise.2]

theorem log_19_7 : ((99852883:ℝ)/100000000) ≤ log ((19:ℝ)/7) ∧ log ((19:ℝ)/7) ≤ ((24963221:ℝ)/25000000) := by
  have hs : ((305381649551:ℝ)/1000000000000) ≤ log ((19:ℝ)/14) ∧ log ((19:ℝ)/14) ≤ ((19086353097:ℝ)/62500000000) := by
    apply log_interval_of_atanh ((19:ℝ)/14) (by norm_num) 10
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have he : log ((19:ℝ)/7) = log ((19:ℝ)/14)+1*log (2:ℝ) := by
    rw [show ((19:ℝ)/7) = ((19:ℝ)/14)*(2:ℝ)^1 by norm_num, log_mul (by norm_num) (by norm_num), log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hs.1, hs.2, log_two_precise.1, log_two_precise.2]

theorem log_39_14 : ((102450431:ℝ)/100000000) ≤ log ((39:ℝ)/14) ∧ log ((39:ℝ)/14) ≤ ((400197:ℝ)/390625) := by
  have hs : ((165678567977:ℝ)/500000000000) ≤ log ((39:ℝ)/28) ∧ log ((39:ℝ)/28) ≤ ((66271427191:ℝ)/200000000000) := by
    apply log_interval_of_atanh ((39:ℝ)/28) (by norm_num) 10
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have he : log ((39:ℝ)/14) = log ((39:ℝ)/28)+1*log (2:ℝ) := by
    rw [show ((39:ℝ)/14) = ((39:ℝ)/28)*(2:ℝ)^1 by norm_num, log_mul (by norm_num) (by norm_num), log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hs.1, hs.2, log_two_precise.1, log_two_precise.2]

theorem log_14_5 : ((102961941:ℝ)/100000000) ≤ log ((14:ℝ)/5) ∧ log ((14:ℝ)/5) ≤ ((51480971:ℝ)/50000000) := by
  have hs : ((336472236621:ℝ)/1000000000000) ≤ log ((7:ℝ)/5) ∧ log ((7:ℝ)/5) ≤ ((168236118311:ℝ)/500000000000) := by
    apply log_interval_of_atanh ((7:ℝ)/5) (by norm_num) 10
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have he : log ((14:ℝ)/5) = log ((7:ℝ)/5)+1*log (2:ℝ) := by
    rw [show ((14:ℝ)/5) = ((7:ℝ)/5)*(2:ℝ)^1 by norm_num, log_mul (by norm_num) (by norm_num), log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hs.1, hs.2, log_two_precise.1, log_two_precise.2]

theorem log_20_7 : ((26245553:ℝ)/25000000) ≤ log ((20:ℝ)/7) ∧ log ((20:ℝ)/7) ≤ ((104982213:ℝ)/100000000) := by
  have hs : ((178337471969:ℝ)/500000000000) ≤ log ((10:ℝ)/7) ∧ log ((10:ℝ)/7) ≤ ((356674943939:ℝ)/1000000000000) := by
    apply log_interval_of_atanh ((10:ℝ)/7) (by norm_num) 11
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have he : log ((20:ℝ)/7) = log ((10:ℝ)/7)+1*log (2:ℝ) := by
    rw [show ((20:ℝ)/7) = ((10:ℝ)/7)*(2:ℝ)^1 by norm_num, log_mul (by norm_num) (by norm_num), log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hs.1, hs.2, log_two_precise.1, log_two_precise.2]

theorem log_41_14 : ((107451473:ℝ)/100000000) ≤ log ((41:ℝ)/14) ∧ log ((41:ℝ)/14) ≤ ((53725737:ℝ)/50000000) := by
  have hs : ((381367556529:ℝ)/1000000000000) ≤ log ((41:ℝ)/28) ∧ log ((41:ℝ)/28) ≤ ((38136755653:ℝ)/100000000000) := by
    apply log_interval_of_atanh ((41:ℝ)/28) (by norm_num) 11
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have he : log ((41:ℝ)/14) = log ((41:ℝ)/28)+1*log (2:ℝ) := by
    rw [show ((41:ℝ)/14) = ((41:ℝ)/28)*(2:ℝ)^1 by norm_num, log_mul (by norm_num) (by norm_num), log_pow]
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

theorem log_43_14 : ((56107139:ℝ)/50000000) ≤ log ((43:ℝ)/14) ∧ log ((43:ℝ)/14) ≤ ((112214279:ℝ)/100000000) := by
  have hs : ((214497802759:ℝ)/500000000000) ≤ log ((43:ℝ)/28) ∧ log ((43:ℝ)/28) ≤ ((428995605519:ℝ)/1000000000000) := by
    apply log_interval_of_atanh ((43:ℝ)/28) (by norm_num) 11
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have he : log ((43:ℝ)/14) = log ((43:ℝ)/28)+1*log (2:ℝ) := by
    rw [show ((43:ℝ)/14) = ((43:ℝ)/28)*(2:ℝ)^1 by norm_num, log_mul (by norm_num) (by norm_num), log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hs.1, hs.2, log_two_precise.1, log_two_precise.2]

theorem log_7_2 : ((15659537:ℝ)/12500000) ≤ log ((7:ℝ)/2) ∧ log ((7:ℝ)/2) ≤ ((125276297:ℝ)/100000000) := by
  have hs : ((111923157587:ℝ)/200000000000) ≤ log ((7:ℝ)/4) ∧ log ((7:ℝ)/4) ≤ ((17487993373:ℝ)/31250000000) := by
    apply log_interval_of_atanh ((7:ℝ)/4) (by norm_num) 13
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have he : log ((7:ℝ)/2) = log ((7:ℝ)/4)+1*log (2:ℝ) := by
    rw [show ((7:ℝ)/2) = ((7:ℝ)/4)*(2:ℝ)^1 by norm_num, log_mul (by norm_num) (by norm_num), log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hs.1, hs.2, log_two_precise.1, log_two_precise.2]

theorem log_14_3 : ((19255563:ℝ)/12500000) ≤ log ((14:ℝ)/3) ∧ log ((14:ℝ)/3) ≤ ((30808901:ℝ)/20000000) := by
  have hs : ((154150679827:ℝ)/1000000000000) ≤ log ((7:ℝ)/6) ∧ log ((7:ℝ)/6) ≤ ((38537669957:ℝ)/250000000000) := by
    apply log_interval_of_atanh ((7:ℝ)/6) (by norm_num) 8
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have he : log ((14:ℝ)/3) = log ((7:ℝ)/6)+2*log (2:ℝ) := by
    rw [show ((14:ℝ)/3) = ((7:ℝ)/6)*(2:ℝ)^2 by norm_num, log_mul (by norm_num) (by norm_num), log_pow]
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

theorem log_14_1 : ((65976433:ℝ)/25000000) ≤ log ((14:ℝ)/1) ∧ log ((14:ℝ)/1) ≤ ((263905733:ℝ)/100000000) := by
  have hs : ((111923157587:ℝ)/200000000000) ≤ log ((7:ℝ)/4) ∧ log ((7:ℝ)/4) ≤ ((17487993373:ℝ)/31250000000) := by
    apply log_interval_of_atanh ((7:ℝ)/4) (by norm_num) 13
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have he : log ((14:ℝ)/1) = log ((7:ℝ)/4)+3*log (2:ℝ) := by
    rw [show ((14:ℝ)/1) = ((7:ℝ)/4)*(2:ℝ)^3 by norm_num, log_mul (by norm_num) (by norm_num), log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hs.1, hs.2, log_two_precise.1, log_two_precise.2]

theorem log_196_13 : ((27131653:ℝ)/10000000) ≤ log ((196:ℝ)/13) ∧ log ((196:ℝ)/13) ≤ ((271316531:ℝ)/100000000) := by
  have hs : ((633723760089:ℝ)/1000000000000) ≤ log ((49:ℝ)/26) ∧ log ((49:ℝ)/26) ≤ ((63372376009:ℝ)/100000000000) := by
    apply log_interval_of_atanh ((49:ℝ)/26) (by norm_num) 14
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have he : log ((196:ℝ)/13) = log ((49:ℝ)/26)+3*log (2:ℝ) := by
    rw [show ((196:ℝ)/13) = ((49:ℝ)/26)*(2:ℝ)^3 by norm_num, log_mul (by norm_num) (by norm_num), log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hs.1, hs.2, log_two_precise.1, log_two_precise.2]

theorem gamma_bounds : ((33932807:ℝ)/100000000000) ≤ gamma 14 ∧ gamma 14 ≤ ((4241601:ℝ)/12500000000) := by
  have h := log_196_13
  unfold gamma logGamma
  rw [← log_div (by norm_num : (14:ℝ)^2 ≠ 0) (by norm_num : (14:ℝ)-1 ≠ 0)]
  norm_num at h ⊢
  constructor <;> linarith

theorem ratio_log_lower_3 : ((19255563:ℝ)/12500000) ≤ log ((14:ℝ)/3) := by
  convert log_14_3.1 using 1 <;> norm_num

theorem ratio_log_lower_4 : ((15659537:ℝ)/12500000) ≤ log ((14:ℝ)/4) := by
  convert log_7_2.1 using 1 <;> norm_num

theorem ratio_log_lower_5 : ((102961941:ℝ)/100000000) ≤ log ((14:ℝ)/5) := by
  convert log_14_5.1 using 1 <;> norm_num

theorem ratio_log_lower_6 : ((42364893:ℝ)/50000000) ≤ log ((14:ℝ)/6) := by
  convert log_7_3.1 using 1 <;> norm_num

theorem ratio_log_lower_7 : ((34657359:ℝ)/50000000) ≤ log ((14:ℝ)/7) := by
  convert log_2_1.1 using 1 <;> norm_num

theorem ratio_log_lower_8 : ((27980789:ℝ)/50000000) ≤ log ((14:ℝ)/8) := by
  convert log_7_4.1 using 1 <;> norm_num

theorem ratio_log_lower_9 : ((1767331:ℝ)/4000000) ≤ log ((14:ℝ)/9) := by
  convert log_14_9.1 using 1 <;> norm_num

theorem ratio_log_lower_10 : ((33647223:ℝ)/100000000) ≤ log ((14:ℝ)/10) := by
  convert log_7_5.1 using 1 <;> norm_num

theorem ratio_log_lower_11 : ((4823241:ℝ)/20000000) ≤ log ((14:ℝ)/11) := by
  convert log_14_11.1 using 1 <;> norm_num

theorem ratio_log_lower_12 : ((15415067:ℝ)/100000000) ≤ log ((14:ℝ)/12) := by
  convert log_7_6.1 using 1 <;> norm_num

theorem ratio_log_lower_13 : ((7410797:ℝ)/100000000) ≤ log ((14:ℝ)/13) := by
  convert log_14_13.1 using 1 <;> norm_num

theorem ratio_log_lower_14 : ((0:ℝ)/1) ≤ log ((14:ℝ)/14) := by
  norm_num

theorem ratio_log_lower_15 : ((-862411:ℝ)/12500000) ≤ log ((14:ℝ)/15) := by
  rw [show (14:ℝ)/15 = (((15:ℝ)/14))⁻¹ by norm_num, log_inv]
  linarith [log_15_14.2]

theorem ratio_log_lower_16 : ((-667657:ℝ)/5000000) ≤ log ((14:ℝ)/16) := by
  rw [show (14:ℝ)/16 = (((8:ℝ)/7))⁻¹ by norm_num, log_inv]
  linarith [log_8_7.2]

theorem ratio_log_lower_17 : ((-9707801:ℝ)/50000000) ≤ log ((14:ℝ)/17) := by
  rw [show (14:ℝ)/17 = (((17:ℝ)/14))⁻¹ by norm_num, log_inv]
  linarith [log_17_14.2]

theorem ratio_log_lower_18 : ((-25131443:ℝ)/100000000) ≤ log ((14:ℝ)/18) := by
  rw [show (14:ℝ)/18 = (((9:ℝ)/7))⁻¹ by norm_num, log_inv]
  linarith [log_9_7.2]

theorem ratio_log_lower_19 : ((-6107633:ℝ)/20000000) ≤ log ((14:ℝ)/19) := by
  rw [show (14:ℝ)/19 = (((19:ℝ)/14))⁻¹ by norm_num, log_inv]
  linarith [log_19_14.2]

theorem ratio_log_lower_20 : ((-7133499:ℝ)/20000000) ≤ log ((14:ℝ)/20) := by
  rw [show (14:ℝ)/20 = (((10:ℝ)/7))⁻¹ by norm_num, log_inv]
  linarith [log_10_7.2]

theorem ratio_log_lower_21 : ((-40546511:ℝ)/100000000) ≤ log ((14:ℝ)/21) := by
  rw [show (14:ℝ)/21 = (((3:ℝ)/2))⁻¹ by norm_num, log_inv]
  linarith [log_3_2.2]

theorem ratio_log_lower_22 : ((-45198513:ℝ)/100000000) ≤ log ((14:ℝ)/22) := by
  rw [show (14:ℝ)/22 = (((11:ℝ)/7))⁻¹ by norm_num, log_inv]
  linarith [log_11_7.2]

theorem ratio_log_lower_23 : ((-49643689:ℝ)/100000000) ≤ log ((14:ℝ)/23) := by
  rw [show (14:ℝ)/23 = (((23:ℝ)/14))⁻¹ by norm_num, log_inv]
  linarith [log_23_14.2]

theorem ratio_log_lower_24 : ((-53899651:ℝ)/100000000) ≤ log ((14:ℝ)/24) := by
  rw [show (14:ℝ)/24 = (((12:ℝ)/7))⁻¹ by norm_num, log_inv]
  linarith [log_12_7.2]

theorem ratio_log_lower_25 : ((-1159637:ℝ)/2000000) ≤ log ((14:ℝ)/25) := by
  rw [show (14:ℝ)/25 = (((25:ℝ)/14))⁻¹ by norm_num, log_inv]
  linarith [log_25_14.2]

theorem ratio_log_lower_26 : ((-61903921:ℝ)/100000000) ≤ log ((14:ℝ)/26) := by
  rw [show (14:ℝ)/26 = (((13:ℝ)/7))⁻¹ by norm_num, log_inv]
  linarith [log_13_7.2]

theorem ratio_log_lower_27 : ((-32838977:ℝ)/50000000) ≤ log ((14:ℝ)/27) := by
  rw [show (14:ℝ)/27 = (((27:ℝ)/14))⁻¹ by norm_num, log_inv]
  linarith [log_27_14.2]

theorem ratio_log_lower_28 : ((-69314719:ℝ)/100000000) ≤ log ((14:ℝ)/28) := by
  rw [show (14:ℝ)/28 = (((2:ℝ)/1))⁻¹ by norm_num, log_inv]
  linarith [log_2_1.2]

theorem ratio_log_lower_29 : ((-72823851:ℝ)/100000000) ≤ log ((14:ℝ)/29) := by
  rw [show (14:ℝ)/29 = (((29:ℝ)/14))⁻¹ by norm_num, log_inv]
  linarith [log_29_14.2]

theorem ratio_log_lower_30 : ((-38107003:ℝ)/50000000) ≤ log ((14:ℝ)/30) := by
  rw [show (14:ℝ)/30 = (((15:ℝ)/7))⁻¹ by norm_num, log_inv]
  linarith [log_15_7.2]

theorem ratio_log_lower_31 : ((-19873247:ℝ)/25000000) ≤ log ((14:ℝ)/31) := by
  rw [show (14:ℝ)/31 = (((31:ℝ)/14))⁻¹ by norm_num, log_inv]
  linarith [log_31_14.2]

theorem ratio_log_lower_32 : ((-41333929:ℝ)/50000000) ≤ log ((14:ℝ)/32) := by
  rw [show (14:ℝ)/32 = (((16:ℝ)/7))⁻¹ by norm_num, log_inv]
  linarith [log_16_7.2]

theorem ratio_log_lower_33 : ((-669883:ℝ)/781250) ≤ log ((14:ℝ)/33) := by
  rw [show (14:ℝ)/33 = (((33:ℝ)/14))⁻¹ by norm_num, log_inv]
  linarith [log_33_14.2]

theorem ratio_log_lower_34 : ((-1109129:ℝ)/1250000) ≤ log ((14:ℝ)/34) := by
  rw [show (14:ℝ)/34 = (((17:ℝ)/7))⁻¹ by norm_num, log_inv]
  linarith [log_17_7.2]

theorem ratio_log_lower_35 : ((-45814537:ℝ)/50000000) ≤ log ((14:ℝ)/35) := by
  rw [show (14:ℝ)/35 = (((5:ℝ)/2))⁻¹ by norm_num, log_inv]
  linarith [log_5_2.2]

theorem ratio_log_lower_36 : ((-94446161:ℝ)/100000000) ≤ log ((14:ℝ)/36) := by
  rw [show (14:ℝ)/36 = (((18:ℝ)/7))⁻¹ by norm_num, log_inv]
  linarith [log_18_7.2]

theorem ratio_log_lower_37 : ((-97186059:ℝ)/100000000) ≤ log ((14:ℝ)/37) := by
  rw [show (14:ℝ)/37 = (((37:ℝ)/14))⁻¹ by norm_num, log_inv]
  linarith [log_37_14.2]

theorem ratio_log_lower_38 : ((-24963221:ℝ)/25000000) ≤ log ((14:ℝ)/38) := by
  rw [show (14:ℝ)/38 = (((19:ℝ)/7))⁻¹ by norm_num, log_inv]
  linarith [log_19_7.2]

theorem ratio_log_lower_39 : ((-400197:ℝ)/390625) ≤ log ((14:ℝ)/39) := by
  rw [show (14:ℝ)/39 = (((39:ℝ)/14))⁻¹ by norm_num, log_inv]
  linarith [log_39_14.2]

theorem ratio_log_lower_40 : ((-104982213:ℝ)/100000000) ≤ log ((14:ℝ)/40) := by
  rw [show (14:ℝ)/40 = (((20:ℝ)/7))⁻¹ by norm_num, log_inv]
  linarith [log_20_7.2]

theorem ratio_log_lower_41 : ((-53725737:ℝ)/50000000) ≤ log ((14:ℝ)/41) := by
  rw [show (14:ℝ)/41 = (((41:ℝ)/14))⁻¹ by norm_num, log_inv]
  linarith [log_41_14.2]

theorem ratio_log_lower_42 : ((-109861229:ℝ)/100000000) ≤ log ((14:ℝ)/42) := by
  rw [show (14:ℝ)/42 = (((3:ℝ)/1))⁻¹ by norm_num, log_inv]
  linarith [log_3_1.2]

theorem ratio_log_lower_43 : ((-112214279:ℝ)/100000000) ≤ log ((14:ℝ)/43) := by
  rw [show (14:ℝ)/43 = (((43:ℝ)/14))⁻¹ by norm_num, log_inv]
  linarith [log_43_14.2]

end SparseComponent.TotalFamily.Density14
