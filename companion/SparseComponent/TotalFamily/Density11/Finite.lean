import SparseComponent.TotalFamily.Density11.LogBounds
import SparseComponent.TotalFamily.FiniteCertificateTools

namespace SparseComponent.TotalFamily.Density11
open Finset Matrix Real TotalOnes
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

noncomputable def poly (x y : ℝ) : ℝ :=
  (((0:ℝ)/1)+((-14641:ℝ)/2)*gamma 11)*x^3*y^1 +
  (((0:ℝ)/1)+((-131769:ℝ)/25)*gamma 11)*x^3*y^0 +
  (((0:ℝ)/1)+((87846:ℝ)/5)*gamma 11)*x^2*y^1 +
  (((0:ℝ)/1)+((-15972:ℝ)/25)*gamma 11)*x^2*y^0 +
  (((0:ℝ)/1)+((-14641:ℝ)/2)*gamma 11)*x^1*y^3 +
  (((0:ℝ)/1)+((87846:ℝ)/5)*gamma 11)*x^1*y^2 +
  (((-121:ℝ)/10)+((-1452:ℝ)/5)*gamma 11)*x^1*y^1 +
  (((1:ℝ)/10)+((-3509:ℝ)/25)*gamma 11)*x^1*y^0 +
  (((0:ℝ)/1)+((-131769:ℝ)/25)*gamma 11)*x^0*y^3 +
  (((0:ℝ)/1)+((-15972:ℝ)/25)*gamma 11)*x^0*y^2 +
  (((1:ℝ)/10)+((-3509:ℝ)/25)*gamma 11)*x^0*y^1 +
  (((9:ℝ)/110)+((21:ℝ)/1)*gamma 11)*x^0*y^0

theorem poly_identity (x y : ℝ) : polynomialModel 11 (linearAnchor 11) x y = poly x y := by
  unfold polynomialModel linearAnchor poly
  generalize gamma 11 = g
  norm_num
  ring

theorem edge_value (d c : ℝ) (hd : d ≠ 0) (hc : c ≠ 0) :
    edgeCost 11 (linearAnchor 11) d c = poly (1/d) (1/c)+(1/d)*log (11/d)+(1/c)*log (11/c) := by
  have h := edgeCost_reciprocal 11 (1/d) (1/c) (by norm_num) (one_div_ne_zero hd) (one_div_ne_zero hc) (linearAnchor 11)
  simp only [one_div_one_div] at h
  rw [h, polynomial_edge_identity 11 (1/d) (1/c) (by norm_num), poly_identity]
  simp only [div_eq_mul_inv, one_mul]

theorem edge_value_model (d c : ℝ) (hd : d ≠ 0) (hc : c ≠ 0) :
    edgeCost 11 (linearAnchor 11) d c = polynomialModel 11 (linearAnchor 11) (1/d) (1/c)+(1/d)*log (11/d)+(1/c)*log (11/c) := by
  rw [edge_value d c hd hc, poly_identity]

def anchorRat (z : ℚ) : ℚ := 2/(5*11)+(3/5)*z
def baseRat (x y : ℚ) : ℚ := 2/11-1/(11-1)+(x+y)/(11-1)-11^2/(11-1)*x*y
def slopeRat (x y : ℚ) : ℚ :=
  2*11-1-11^2*(x+y)-2*11^2*(11-1)*x*y +
  11^4*(-x*(anchorRat x)^2-y*(anchorRat y)^2+
    2*x*y*(anchorRat x+anchorRat y)-(x^3*y+x*y^3)/2)
def gammaLoRat : ℚ := ((2794187:ℚ)/4000000000)
def gammaHiRat : ℚ := ((17463669:ℚ)/25000000000)
def logLoRat : ℕ → ℚ
  | 3 => ((64964149:ℚ)/50000000)
  | 4 => ((101160091:ℚ)/100000000)
  | 5 => ((9855717:ℚ)/12500000)
  | 6 => ((3030679:ℚ)/5000000)
  | 7 => ((2824907:ℚ)/6250000)
  | 8 => ((31845373:ℚ)/100000000)
  | 9 => ((20067069:ℚ)/100000000)
  | 10 => ((9531017:ℚ)/100000000)
  | 11 => ((0:ℚ)/1)
  | 12 => ((-4350569:ℚ)/50000000)
  | 13 => ((-16705409:ℚ)/100000000)
  | 14 => ((-12058103:ℚ)/50000000)
  | 15 => ((-31015493:ℚ)/100000000)
  | 16 => ((-7493869:ℚ)/20000000)
  | 17 => ((-1360369:ℚ)/3125000)
  | 18 => ((-49247649:ℚ)/100000000)
  | 19 => ((-54654371:ℚ)/100000000)
  | 20 => ((-59783701:ℚ)/100000000)
  | 21 => ((-64662717:ℚ)/100000000)
  | 22 => ((-69314719:ℚ)/100000000)
  | 23 => ((-14751979:ℚ)/20000000)
  | 24 => ((-4875991:ℚ)/6250000)
  | 25 => ((-10262257:ℚ)/12500000)
  | 26 => ((-86020127:ℚ)/100000000)
  | 27 => ((-1122427:ℚ)/1250000)
  | 28 => ((-23357731:ℚ)/25000000)
  | 29 => ((-12117507:ℚ)/12500000)
  | 30 => ((-100330211:ℚ)/100000000)
  | 31 => ((-51804597:ℚ)/50000000)
  | 32 => ((-1668501:ℚ)/1562500)
  | 33 => ((-109861229:ℚ)/100000000)
  | _ => 0

theorem model_rational (x y : ℚ) :
    polynomialModel 11 (linearAnchor 11) (x:ℝ) (y:ℝ) = (baseRat x y:ℝ)+(slopeRat x y:ℝ)*gamma 11 := by
  unfold polynomialModel linearAnchor baseRat slopeRat anchorRat
  generalize gamma 11 = g
  push_cast
  norm_num
  ring

theorem gamma_rat_bounds : (gammaLoRat:ℝ) ≤ gamma 11 ∧ gamma 11 ≤ (gammaHiRat:ℝ) := by
  norm_num only [gammaLoRat, gammaHiRat, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg]
  exact gamma_bounds

theorem degree_log_lower (d : ℕ) (hd : 3 ≤ d) (hD : d ≤ 33) :
    (logLoRat d:ℝ) ≤ log (11/(d:ℝ)) := by
  interval_cases d
  · convert ratio_log_lower_3 using 1 <;> norm_num [logLoRat]
  · convert ratio_log_lower_4 using 1 <;> norm_num [logLoRat]
  · convert ratio_log_lower_5 using 1 <;> norm_num [logLoRat]
  · convert ratio_log_lower_6 using 1 <;> norm_num [logLoRat]
  · convert ratio_log_lower_7 using 1 <;> norm_num [logLoRat]
  · convert ratio_log_lower_8 using 1 <;> norm_num [logLoRat]
  · convert ratio_log_lower_9 using 1 <;> norm_num [logLoRat]
  · convert ratio_log_lower_10 using 1 <;> norm_num [logLoRat]
  · convert ratio_log_lower_11 using 1 <;> norm_num [logLoRat]
  · convert ratio_log_lower_12 using 1 <;> norm_num [logLoRat]
  · convert ratio_log_lower_13 using 1 <;> norm_num [logLoRat]
  · convert ratio_log_lower_14 using 1 <;> norm_num [logLoRat]
  · convert ratio_log_lower_15 using 1 <;> norm_num [logLoRat]
  · convert ratio_log_lower_16 using 1 <;> norm_num [logLoRat]
  · convert ratio_log_lower_17 using 1 <;> norm_num [logLoRat]
  · convert ratio_log_lower_18 using 1 <;> norm_num [logLoRat]
  · convert ratio_log_lower_19 using 1 <;> norm_num [logLoRat]
  · convert ratio_log_lower_20 using 1 <;> norm_num [logLoRat]
  · convert ratio_log_lower_21 using 1 <;> norm_num [logLoRat]
  · convert ratio_log_lower_22 using 1 <;> norm_num [logLoRat]
  · convert ratio_log_lower_23 using 1 <;> norm_num [logLoRat]
  · convert ratio_log_lower_24 using 1 <;> norm_num [logLoRat]
  · convert ratio_log_lower_25 using 1 <;> norm_num [logLoRat]
  · convert ratio_log_lower_26 using 1 <;> norm_num [logLoRat]
  · convert ratio_log_lower_27 using 1 <;> norm_num [logLoRat]
  · convert ratio_log_lower_28 using 1 <;> norm_num [logLoRat]
  · convert ratio_log_lower_29 using 1 <;> norm_num [logLoRat]
  · convert ratio_log_lower_30 using 1 <;> norm_num [logLoRat]
  · convert ratio_log_lower_31 using 1 <;> norm_num [logLoRat]
  · convert ratio_log_lower_32 using 1 <;> norm_num [logLoRat]
  · convert ratio_log_lower_33 using 1 <;> norm_num [logLoRat]

/-- The finite rational table is checked by kernel reduction; no native evaluator is trusted. -/
theorem finite_gate_row_3 : ∀ c : Fin 34, 3 ≤ c.val →
    ¬(3=11 ∧ c.val=11) →
    0 < min (baseRat (1/(3:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(3:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(3:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(3:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(3:ℚ))*logLoRat 3+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_4 : ∀ c : Fin 34, 3 ≤ c.val →
    ¬(4=11 ∧ c.val=11) →
    0 < min (baseRat (1/(4:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(4:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(4:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(4:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(4:ℚ))*logLoRat 4+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_5 : ∀ c : Fin 34, 3 ≤ c.val →
    ¬(5=11 ∧ c.val=11) →
    0 < min (baseRat (1/(5:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(5:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(5:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(5:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(5:ℚ))*logLoRat 5+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_6 : ∀ c : Fin 34, 3 ≤ c.val →
    ¬(6=11 ∧ c.val=11) →
    0 < min (baseRat (1/(6:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(6:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(6:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(6:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(6:ℚ))*logLoRat 6+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_7 : ∀ c : Fin 34, 3 ≤ c.val →
    ¬(7=11 ∧ c.val=11) →
    0 < min (baseRat (1/(7:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(7:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(7:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(7:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(7:ℚ))*logLoRat 7+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_8 : ∀ c : Fin 34, 3 ≤ c.val →
    ¬(8=11 ∧ c.val=11) →
    0 < min (baseRat (1/(8:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(8:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(8:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(8:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(8:ℚ))*logLoRat 8+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_9 : ∀ c : Fin 34, 3 ≤ c.val →
    ¬(9=11 ∧ c.val=11) →
    0 < min (baseRat (1/(9:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(9:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(9:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(9:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(9:ℚ))*logLoRat 9+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_10 : ∀ c : Fin 34, 3 ≤ c.val →
    ¬(10=11 ∧ c.val=11) →
    0 < min (baseRat (1/(10:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(10:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(10:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(10:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(10:ℚ))*logLoRat 10+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_11 : ∀ c : Fin 34, 3 ≤ c.val →
    ¬(11=11 ∧ c.val=11) →
    0 < min (baseRat (1/(11:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(11:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(11:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(11:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(11:ℚ))*logLoRat 11+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_12 : ∀ c : Fin 34, 3 ≤ c.val →
    ¬(12=11 ∧ c.val=11) →
    0 < min (baseRat (1/(12:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(12:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(12:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(12:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(12:ℚ))*logLoRat 12+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_13 : ∀ c : Fin 34, 3 ≤ c.val →
    ¬(13=11 ∧ c.val=11) →
    0 < min (baseRat (1/(13:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(13:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(13:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(13:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(13:ℚ))*logLoRat 13+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_14 : ∀ c : Fin 34, 3 ≤ c.val →
    ¬(14=11 ∧ c.val=11) →
    0 < min (baseRat (1/(14:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(14:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(14:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(14:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(14:ℚ))*logLoRat 14+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_15 : ∀ c : Fin 34, 3 ≤ c.val →
    ¬(15=11 ∧ c.val=11) →
    0 < min (baseRat (1/(15:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(15:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(15:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(15:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(15:ℚ))*logLoRat 15+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_16 : ∀ c : Fin 34, 3 ≤ c.val →
    ¬(16=11 ∧ c.val=11) →
    0 < min (baseRat (1/(16:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(16:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(16:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(16:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(16:ℚ))*logLoRat 16+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_17 : ∀ c : Fin 34, 3 ≤ c.val →
    ¬(17=11 ∧ c.val=11) →
    0 < min (baseRat (1/(17:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(17:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(17:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(17:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(17:ℚ))*logLoRat 17+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_18 : ∀ c : Fin 34, 3 ≤ c.val →
    ¬(18=11 ∧ c.val=11) →
    0 < min (baseRat (1/(18:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(18:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(18:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(18:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(18:ℚ))*logLoRat 18+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_19 : ∀ c : Fin 34, 3 ≤ c.val →
    ¬(19=11 ∧ c.val=11) →
    0 < min (baseRat (1/(19:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(19:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(19:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(19:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(19:ℚ))*logLoRat 19+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_20 : ∀ c : Fin 34, 3 ≤ c.val →
    ¬(20=11 ∧ c.val=11) →
    0 < min (baseRat (1/(20:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(20:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(20:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(20:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(20:ℚ))*logLoRat 20+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_21 : ∀ c : Fin 34, 3 ≤ c.val →
    ¬(21=11 ∧ c.val=11) →
    0 < min (baseRat (1/(21:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(21:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(21:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(21:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(21:ℚ))*logLoRat 21+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_22 : ∀ c : Fin 34, 3 ≤ c.val →
    ¬(22=11 ∧ c.val=11) →
    0 < min (baseRat (1/(22:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(22:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(22:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(22:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(22:ℚ))*logLoRat 22+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_23 : ∀ c : Fin 34, 3 ≤ c.val →
    ¬(23=11 ∧ c.val=11) →
    0 < min (baseRat (1/(23:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(23:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(23:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(23:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(23:ℚ))*logLoRat 23+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_24 : ∀ c : Fin 34, 3 ≤ c.val →
    ¬(24=11 ∧ c.val=11) →
    0 < min (baseRat (1/(24:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(24:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(24:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(24:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(24:ℚ))*logLoRat 24+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_25 : ∀ c : Fin 34, 3 ≤ c.val →
    ¬(25=11 ∧ c.val=11) →
    0 < min (baseRat (1/(25:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(25:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(25:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(25:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(25:ℚ))*logLoRat 25+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_26 : ∀ c : Fin 34, 3 ≤ c.val →
    ¬(26=11 ∧ c.val=11) →
    0 < min (baseRat (1/(26:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(26:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(26:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(26:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(26:ℚ))*logLoRat 26+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_27 : ∀ c : Fin 34, 3 ≤ c.val →
    ¬(27=11 ∧ c.val=11) →
    0 < min (baseRat (1/(27:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(27:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(27:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(27:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(27:ℚ))*logLoRat 27+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_28 : ∀ c : Fin 34, 3 ≤ c.val →
    ¬(28=11 ∧ c.val=11) →
    0 < min (baseRat (1/(28:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(28:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(28:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(28:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(28:ℚ))*logLoRat 28+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_29 : ∀ c : Fin 34, 3 ≤ c.val →
    ¬(29=11 ∧ c.val=11) →
    0 < min (baseRat (1/(29:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(29:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(29:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(29:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(29:ℚ))*logLoRat 29+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_30 : ∀ c : Fin 34, 3 ≤ c.val →
    ¬(30=11 ∧ c.val=11) →
    0 < min (baseRat (1/(30:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(30:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(30:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(30:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(30:ℚ))*logLoRat 30+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_31 : ∀ c : Fin 34, 3 ≤ c.val →
    ¬(31=11 ∧ c.val=11) →
    0 < min (baseRat (1/(31:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(31:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(31:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(31:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(31:ℚ))*logLoRat 31+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_32 : ∀ c : Fin 34, 3 ≤ c.val →
    ¬(32=11 ∧ c.val=11) →
    0 < min (baseRat (1/(32:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(32:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(32:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(32:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(32:ℚ))*logLoRat 32+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_33 : ∀ c : Fin 34, 3 ≤ c.val →
    ¬(33=11 ∧ c.val=11) →
    0 < min (baseRat (1/(33:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(33:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(33:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(33:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(33:ℚ))*logLoRat 33+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate : ∀ d c : Fin 34, 3 ≤ d.val → 3 ≤ c.val →
    ¬(d.val=11 ∧ c.val=11) →
    0 < min (baseRat (1/(d.val:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(d.val:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(d.val:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(d.val:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(d.val:ℚ))*logLoRat d.val+(1/(c.val:ℚ))*logLoRat c.val := by
  intro d c hd hc hn
  have hdN : d.val ≤ 33 := by omega
  generalize hk : d.val = k at hd hdN hn ⊢
  interval_cases k
  · simpa only [Nat.cast_ofNat] using finite_gate_row_3 c hc hn
  · simpa only [Nat.cast_ofNat] using finite_gate_row_4 c hc hn
  · simpa only [Nat.cast_ofNat] using finite_gate_row_5 c hc hn
  · simpa only [Nat.cast_ofNat] using finite_gate_row_6 c hc hn
  · simpa only [Nat.cast_ofNat] using finite_gate_row_7 c hc hn
  · simpa only [Nat.cast_ofNat] using finite_gate_row_8 c hc hn
  · simpa only [Nat.cast_ofNat] using finite_gate_row_9 c hc hn
  · simpa only [Nat.cast_ofNat] using finite_gate_row_10 c hc hn
  · simpa only [Nat.cast_ofNat] using finite_gate_row_11 c hc hn
  · simpa only [Nat.cast_ofNat] using finite_gate_row_12 c hc hn
  · simpa only [Nat.cast_ofNat] using finite_gate_row_13 c hc hn
  · simpa only [Nat.cast_ofNat] using finite_gate_row_14 c hc hn
  · simpa only [Nat.cast_ofNat] using finite_gate_row_15 c hc hn
  · simpa only [Nat.cast_ofNat] using finite_gate_row_16 c hc hn
  · simpa only [Nat.cast_ofNat] using finite_gate_row_17 c hc hn
  · simpa only [Nat.cast_ofNat] using finite_gate_row_18 c hc hn
  · simpa only [Nat.cast_ofNat] using finite_gate_row_19 c hc hn
  · simpa only [Nat.cast_ofNat] using finite_gate_row_20 c hc hn
  · simpa only [Nat.cast_ofNat] using finite_gate_row_21 c hc hn
  · simpa only [Nat.cast_ofNat] using finite_gate_row_22 c hc hn
  · simpa only [Nat.cast_ofNat] using finite_gate_row_23 c hc hn
  · simpa only [Nat.cast_ofNat] using finite_gate_row_24 c hc hn
  · simpa only [Nat.cast_ofNat] using finite_gate_row_25 c hc hn
  · simpa only [Nat.cast_ofNat] using finite_gate_row_26 c hc hn
  · simpa only [Nat.cast_ofNat] using finite_gate_row_27 c hc hn
  · simpa only [Nat.cast_ofNat] using finite_gate_row_28 c hc hn
  · simpa only [Nat.cast_ofNat] using finite_gate_row_29 c hc hn
  · simpa only [Nat.cast_ofNat] using finite_gate_row_30 c hc hn
  · simpa only [Nat.cast_ofNat] using finite_gate_row_31 c hc hn
  · simpa only [Nat.cast_ofNat] using finite_gate_row_32 c hc hn
  · simpa only [Nat.cast_ofNat] using finite_gate_row_33 c hc hn

theorem finite_strict_nat (d c : ℕ) (hd0 : 3 ≤ d) (hc0 : 3 ≤ c)
    (hdN : d ≤ 33) (hcN : c ≤ 33) (hn : ¬(d=11 ∧ c=11)) :
    0 < edgeCost 11 (linearAnchor 11) d c := by
  have hdp : 0 < d := by omega
  have hcp : 0 < c := by omega
  have hg := finite_gate ⟨d,by omega⟩ ⟨c,by omega⟩ hd0 hc0 hn
  have h := rational_edge_gate (baseRat (1/(d:ℚ)) (1/(c:ℚ)))
    (slopeRat (1/(d:ℚ)) (1/(c:ℚ))) gammaLoRat gammaHiRat
    (1/(d:ℚ)) (1/(c:ℚ)) (logLoRat d) (logLoRat c)
    (gamma 11) (log (11/(d:ℝ))) (log (11/(c:ℝ)))
    (by positivity) (by positivity) gamma_rat_bounds.1 gamma_rat_bounds.2
    (degree_log_lower d hd0 hdN) (degree_log_lower c hc0 hcN) hg
  have hm := model_rational (1/(d:ℚ)) (1/(c:ℚ))
  push_cast at h hm
  rw [edge_value_model d c (by positivity) (by positivity), hm]
  exact h

theorem finite_strict (d c : ℤ) (hd0 : 3 ≤ d) (hc0 : 3 ≤ c)
    (hdN : d ≤ 33) (hcN : c ≤ 33) (hn : ¬(d=11 ∧ c=11)) :
    0 < edgeCost 11 (linearAnchor 11) d c := by
  have hd : (d.toNat:ℤ) = d := Int.toNat_of_nonneg (by omega)
  have hc : (c.toNat:ℤ) = c := Int.toNat_of_nonneg (by omega)
  have h := finite_strict_nat d.toNat c.toNat (by omega) (by omega) (by omega) (by omega)
    (by intro hh; apply hn; constructor <;> omega)
  rw [← hd, ← hc]
  simpa only [Int.cast_natCast] using h

end SparseComponent.TotalFamily.Density11
