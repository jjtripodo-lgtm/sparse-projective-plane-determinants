import SparseComponent.TotalFamily.Density14.LogBounds
import SparseComponent.TotalFamily.FiniteCertificateTools

namespace SparseComponent.TotalFamily.Density14
open Finset Matrix Real TotalOnes
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

noncomputable def poly (x y : ℝ) : ℝ :=
  (((0:ℝ)/1)+((-86436:ℝ)/1)*gamma 14)*x^7*y^0 +
  (((0:ℝ)/1)+((-39788:ℝ)/1)*gamma 14)*x^6*y^0 +
  (((0:ℝ)/1)+((1070993:ℝ)/9)*gamma 14)*x^5*y^0 +
  (((0:ℝ)/1)+((-115248:ℝ)/1)*gamma 14)*x^4*y^1 +
  (((0:ℝ)/1)+((253022:ℝ)/9)*gamma 14)*x^4*y^0 +
  (((0:ℝ)/1)+((-137200:ℝ)/3)*gamma 14)*x^3*y^1 +
  (((0:ℝ)/1)+((-176983:ℝ)/4)*gamma 14)*x^3*y^0 +
  (((0:ℝ)/1)+((247156:ℝ)/3)*gamma 14)*x^2*y^1 +
  (((0:ℝ)/1)+((59267:ℝ)/252)*gamma 14)*x^2*y^0 +
  (((0:ℝ)/1)+((-115248:ℝ)/1)*gamma 14)*x^1*y^4 +
  (((0:ℝ)/1)+((-137200:ℝ)/3)*gamma 14)*x^1*y^3 +
  (((0:ℝ)/1)+((247156:ℝ)/3)*gamma 14)*x^1*y^2 +
  (((-196:ℝ)/13)+((-16604:ℝ)/3)*gamma 14)*x^1*y^1 +
  (((1:ℝ)/13)+((-1385185:ℝ)/7056)*gamma 14)*x^1*y^0 +
  (((0:ℝ)/1)+((-86436:ℝ)/1)*gamma 14)*x^0*y^7 +
  (((0:ℝ)/1)+((-39788:ℝ)/1)*gamma 14)*x^0*y^6 +
  (((0:ℝ)/1)+((1070993:ℝ)/9)*gamma 14)*x^0*y^5 +
  (((0:ℝ)/1)+((253022:ℝ)/9)*gamma 14)*x^0*y^4 +
  (((0:ℝ)/1)+((-176983:ℝ)/4)*gamma 14)*x^0*y^3 +
  (((0:ℝ)/1)+((59267:ℝ)/252)*gamma 14)*x^0*y^2 +
  (((1:ℝ)/13)+((-1385185:ℝ)/7056)*gamma 14)*x^0*y^1 +
  (((6:ℝ)/91)+((27:ℝ)/1)*gamma 14)*x^0*y^0

theorem poly_identity (x y : ℝ) : polynomialModel 14 (cubicAnchor 14) x y = poly x y := by
  unfold polynomialModel cubicAnchor poly
  generalize gamma 14 = g
  norm_num
  ring

theorem edge_value (d c : ℝ) (hd : d ≠ 0) (hc : c ≠ 0) :
    edgeCost 14 (cubicAnchor 14) d c = poly (1/d) (1/c)+(1/d)*log (14/d)+(1/c)*log (14/c) := by
  have h := edgeCost_reciprocal 14 (1/d) (1/c) (by norm_num) (one_div_ne_zero hd) (one_div_ne_zero hc) (cubicAnchor 14)
  simp only [one_div_one_div] at h
  rw [h, polynomial_edge_identity 14 (1/d) (1/c) (by norm_num), poly_identity]
  simp only [div_eq_mul_inv, one_mul]

theorem edge_value_model (d c : ℝ) (hd : d ≠ 0) (hc : c ≠ 0) :
    edgeCost 14 (cubicAnchor 14) d c = polynomialModel 14 (cubicAnchor 14) (1/d) (1/c)+(1/d)*log (14/d)+(1/c)*log (14/c) := by
  rw [edge_value d c hd hc, poly_identity]

def anchorRat (z : ℚ) : ℚ := z-(2/3)*(z-1/14)^2-(3/2)*(z-1/14)^3
def baseRat (x y : ℚ) : ℚ := 2/14-1/(14-1)+(x+y)/(14-1)-14^2/(14-1)*x*y
def slopeRat (x y : ℚ) : ℚ :=
  2*14-1-14^2*(x+y)-2*14^2*(14-1)*x*y +
  14^4*(-x*(anchorRat x)^2-y*(anchorRat y)^2+
    2*x*y*(anchorRat x+anchorRat y)-(x^3*y+x*y^3)/2)
def gammaLoRat : ℚ := ((33932807:ℚ)/100000000000)
def gammaHiRat : ℚ := ((4241601:ℚ)/12500000000)
def logLoRat : ℕ → ℚ
  | 3 => ((19255563:ℚ)/12500000)
  | 4 => ((15659537:ℚ)/12500000)
  | 5 => ((102961941:ℚ)/100000000)
  | 6 => ((42364893:ℚ)/50000000)
  | 7 => ((34657359:ℚ)/50000000)
  | 8 => ((27980789:ℚ)/50000000)
  | 9 => ((1767331:ℚ)/4000000)
  | 10 => ((33647223:ℚ)/100000000)
  | 11 => ((4823241:ℚ)/20000000)
  | 12 => ((15415067:ℚ)/100000000)
  | 13 => ((7410797:ℚ)/100000000)
  | 14 => ((0:ℚ)/1)
  | 15 => ((-862411:ℚ)/12500000)
  | 16 => ((-667657:ℚ)/5000000)
  | 17 => ((-9707801:ℚ)/50000000)
  | 18 => ((-25131443:ℚ)/100000000)
  | 19 => ((-6107633:ℚ)/20000000)
  | 20 => ((-7133499:ℚ)/20000000)
  | 21 => ((-40546511:ℚ)/100000000)
  | 22 => ((-45198513:ℚ)/100000000)
  | 23 => ((-49643689:ℚ)/100000000)
  | 24 => ((-53899651:ℚ)/100000000)
  | 25 => ((-1159637:ℚ)/2000000)
  | 26 => ((-61903921:ℚ)/100000000)
  | 27 => ((-32838977:ℚ)/50000000)
  | 28 => ((-69314719:ℚ)/100000000)
  | 29 => ((-72823851:ℚ)/100000000)
  | 30 => ((-38107003:ℚ)/50000000)
  | 31 => ((-19873247:ℚ)/25000000)
  | 32 => ((-41333929:ℚ)/50000000)
  | 33 => ((-669883:ℚ)/781250)
  | 34 => ((-1109129:ℚ)/1250000)
  | 35 => ((-45814537:ℚ)/50000000)
  | 36 => ((-94446161:ℚ)/100000000)
  | 37 => ((-97186059:ℚ)/100000000)
  | 38 => ((-24963221:ℚ)/25000000)
  | 39 => ((-400197:ℚ)/390625)
  | 40 => ((-104982213:ℚ)/100000000)
  | 41 => ((-53725737:ℚ)/50000000)
  | 42 => ((-109861229:ℚ)/100000000)
  | _ => 0

theorem model_rational (x y : ℚ) :
    polynomialModel 14 (cubicAnchor 14) (x:ℝ) (y:ℝ) = (baseRat x y:ℝ)+(slopeRat x y:ℝ)*gamma 14 := by
  unfold polynomialModel cubicAnchor baseRat slopeRat anchorRat
  generalize gamma 14 = g
  push_cast
  norm_num
  ring

theorem gamma_rat_bounds : (gammaLoRat:ℝ) ≤ gamma 14 ∧ gamma 14 ≤ (gammaHiRat:ℝ) := by
  norm_num only [gammaLoRat, gammaHiRat, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg]
  exact gamma_bounds

theorem degree_log_lower (d : ℕ) (hd : 3 ≤ d) (hD : d ≤ 42) :
    (logLoRat d:ℝ) ≤ log (14/(d:ℝ)) := by
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
  · convert ratio_log_lower_34 using 1 <;> norm_num [logLoRat]
  · convert ratio_log_lower_35 using 1 <;> norm_num [logLoRat]
  · convert ratio_log_lower_36 using 1 <;> norm_num [logLoRat]
  · convert ratio_log_lower_37 using 1 <;> norm_num [logLoRat]
  · convert ratio_log_lower_38 using 1 <;> norm_num [logLoRat]
  · convert ratio_log_lower_39 using 1 <;> norm_num [logLoRat]
  · convert ratio_log_lower_40 using 1 <;> norm_num [logLoRat]
  · convert ratio_log_lower_41 using 1 <;> norm_num [logLoRat]
  · convert ratio_log_lower_42 using 1 <;> norm_num [logLoRat]

/-- The finite rational table is checked by kernel reduction; no native evaluator is trusted. -/
theorem finite_gate_row_3 : ∀ c : Fin 43, 3 ≤ c.val →
    ¬(3=14 ∧ c.val=14) →
    0 < min (baseRat (1/(3:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(3:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(3:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(3:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(3:ℚ))*logLoRat 3+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_4 : ∀ c : Fin 43, 3 ≤ c.val →
    ¬(4=14 ∧ c.val=14) →
    0 < min (baseRat (1/(4:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(4:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(4:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(4:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(4:ℚ))*logLoRat 4+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_5 : ∀ c : Fin 43, 3 ≤ c.val →
    ¬(5=14 ∧ c.val=14) →
    0 < min (baseRat (1/(5:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(5:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(5:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(5:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(5:ℚ))*logLoRat 5+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_6 : ∀ c : Fin 43, 3 ≤ c.val →
    ¬(6=14 ∧ c.val=14) →
    0 < min (baseRat (1/(6:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(6:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(6:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(6:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(6:ℚ))*logLoRat 6+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_7 : ∀ c : Fin 43, 3 ≤ c.val →
    ¬(7=14 ∧ c.val=14) →
    0 < min (baseRat (1/(7:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(7:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(7:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(7:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(7:ℚ))*logLoRat 7+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_8 : ∀ c : Fin 43, 3 ≤ c.val →
    ¬(8=14 ∧ c.val=14) →
    0 < min (baseRat (1/(8:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(8:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(8:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(8:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(8:ℚ))*logLoRat 8+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_9 : ∀ c : Fin 43, 3 ≤ c.val →
    ¬(9=14 ∧ c.val=14) →
    0 < min (baseRat (1/(9:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(9:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(9:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(9:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(9:ℚ))*logLoRat 9+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_10 : ∀ c : Fin 43, 3 ≤ c.val →
    ¬(10=14 ∧ c.val=14) →
    0 < min (baseRat (1/(10:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(10:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(10:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(10:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(10:ℚ))*logLoRat 10+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_11 : ∀ c : Fin 43, 3 ≤ c.val →
    ¬(11=14 ∧ c.val=14) →
    0 < min (baseRat (1/(11:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(11:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(11:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(11:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(11:ℚ))*logLoRat 11+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_12 : ∀ c : Fin 43, 3 ≤ c.val →
    ¬(12=14 ∧ c.val=14) →
    0 < min (baseRat (1/(12:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(12:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(12:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(12:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(12:ℚ))*logLoRat 12+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_13 : ∀ c : Fin 43, 3 ≤ c.val →
    ¬(13=14 ∧ c.val=14) →
    0 < min (baseRat (1/(13:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(13:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(13:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(13:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(13:ℚ))*logLoRat 13+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_14 : ∀ c : Fin 43, 3 ≤ c.val →
    ¬(14=14 ∧ c.val=14) →
    0 < min (baseRat (1/(14:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(14:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(14:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(14:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(14:ℚ))*logLoRat 14+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_15 : ∀ c : Fin 43, 3 ≤ c.val →
    ¬(15=14 ∧ c.val=14) →
    0 < min (baseRat (1/(15:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(15:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(15:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(15:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(15:ℚ))*logLoRat 15+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_16 : ∀ c : Fin 43, 3 ≤ c.val →
    ¬(16=14 ∧ c.val=14) →
    0 < min (baseRat (1/(16:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(16:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(16:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(16:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(16:ℚ))*logLoRat 16+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_17 : ∀ c : Fin 43, 3 ≤ c.val →
    ¬(17=14 ∧ c.val=14) →
    0 < min (baseRat (1/(17:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(17:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(17:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(17:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(17:ℚ))*logLoRat 17+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_18 : ∀ c : Fin 43, 3 ≤ c.val →
    ¬(18=14 ∧ c.val=14) →
    0 < min (baseRat (1/(18:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(18:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(18:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(18:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(18:ℚ))*logLoRat 18+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_19 : ∀ c : Fin 43, 3 ≤ c.val →
    ¬(19=14 ∧ c.val=14) →
    0 < min (baseRat (1/(19:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(19:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(19:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(19:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(19:ℚ))*logLoRat 19+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_20 : ∀ c : Fin 43, 3 ≤ c.val →
    ¬(20=14 ∧ c.val=14) →
    0 < min (baseRat (1/(20:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(20:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(20:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(20:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(20:ℚ))*logLoRat 20+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_21 : ∀ c : Fin 43, 3 ≤ c.val →
    ¬(21=14 ∧ c.val=14) →
    0 < min (baseRat (1/(21:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(21:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(21:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(21:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(21:ℚ))*logLoRat 21+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_22 : ∀ c : Fin 43, 3 ≤ c.val →
    ¬(22=14 ∧ c.val=14) →
    0 < min (baseRat (1/(22:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(22:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(22:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(22:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(22:ℚ))*logLoRat 22+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_23 : ∀ c : Fin 43, 3 ≤ c.val →
    ¬(23=14 ∧ c.val=14) →
    0 < min (baseRat (1/(23:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(23:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(23:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(23:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(23:ℚ))*logLoRat 23+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_24 : ∀ c : Fin 43, 3 ≤ c.val →
    ¬(24=14 ∧ c.val=14) →
    0 < min (baseRat (1/(24:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(24:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(24:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(24:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(24:ℚ))*logLoRat 24+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_25 : ∀ c : Fin 43, 3 ≤ c.val →
    ¬(25=14 ∧ c.val=14) →
    0 < min (baseRat (1/(25:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(25:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(25:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(25:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(25:ℚ))*logLoRat 25+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_26 : ∀ c : Fin 43, 3 ≤ c.val →
    ¬(26=14 ∧ c.val=14) →
    0 < min (baseRat (1/(26:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(26:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(26:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(26:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(26:ℚ))*logLoRat 26+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_27 : ∀ c : Fin 43, 3 ≤ c.val →
    ¬(27=14 ∧ c.val=14) →
    0 < min (baseRat (1/(27:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(27:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(27:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(27:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(27:ℚ))*logLoRat 27+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_28 : ∀ c : Fin 43, 3 ≤ c.val →
    ¬(28=14 ∧ c.val=14) →
    0 < min (baseRat (1/(28:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(28:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(28:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(28:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(28:ℚ))*logLoRat 28+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_29 : ∀ c : Fin 43, 3 ≤ c.val →
    ¬(29=14 ∧ c.val=14) →
    0 < min (baseRat (1/(29:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(29:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(29:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(29:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(29:ℚ))*logLoRat 29+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_30 : ∀ c : Fin 43, 3 ≤ c.val →
    ¬(30=14 ∧ c.val=14) →
    0 < min (baseRat (1/(30:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(30:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(30:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(30:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(30:ℚ))*logLoRat 30+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_31 : ∀ c : Fin 43, 3 ≤ c.val →
    ¬(31=14 ∧ c.val=14) →
    0 < min (baseRat (1/(31:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(31:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(31:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(31:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(31:ℚ))*logLoRat 31+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_32 : ∀ c : Fin 43, 3 ≤ c.val →
    ¬(32=14 ∧ c.val=14) →
    0 < min (baseRat (1/(32:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(32:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(32:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(32:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(32:ℚ))*logLoRat 32+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_33 : ∀ c : Fin 43, 3 ≤ c.val →
    ¬(33=14 ∧ c.val=14) →
    0 < min (baseRat (1/(33:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(33:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(33:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(33:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(33:ℚ))*logLoRat 33+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_34 : ∀ c : Fin 43, 3 ≤ c.val →
    ¬(34=14 ∧ c.val=14) →
    0 < min (baseRat (1/(34:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(34:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(34:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(34:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(34:ℚ))*logLoRat 34+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_35 : ∀ c : Fin 43, 3 ≤ c.val →
    ¬(35=14 ∧ c.val=14) →
    0 < min (baseRat (1/(35:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(35:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(35:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(35:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(35:ℚ))*logLoRat 35+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_36 : ∀ c : Fin 43, 3 ≤ c.val →
    ¬(36=14 ∧ c.val=14) →
    0 < min (baseRat (1/(36:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(36:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(36:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(36:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(36:ℚ))*logLoRat 36+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_37 : ∀ c : Fin 43, 3 ≤ c.val →
    ¬(37=14 ∧ c.val=14) →
    0 < min (baseRat (1/(37:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(37:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(37:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(37:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(37:ℚ))*logLoRat 37+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_38 : ∀ c : Fin 43, 3 ≤ c.val →
    ¬(38=14 ∧ c.val=14) →
    0 < min (baseRat (1/(38:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(38:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(38:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(38:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(38:ℚ))*logLoRat 38+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_39 : ∀ c : Fin 43, 3 ≤ c.val →
    ¬(39=14 ∧ c.val=14) →
    0 < min (baseRat (1/(39:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(39:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(39:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(39:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(39:ℚ))*logLoRat 39+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_40 : ∀ c : Fin 43, 3 ≤ c.val →
    ¬(40=14 ∧ c.val=14) →
    0 < min (baseRat (1/(40:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(40:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(40:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(40:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(40:ℚ))*logLoRat 40+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_41 : ∀ c : Fin 43, 3 ≤ c.val →
    ¬(41=14 ∧ c.val=14) →
    0 < min (baseRat (1/(41:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(41:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(41:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(41:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(41:ℚ))*logLoRat 41+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_42 : ∀ c : Fin 43, 3 ≤ c.val →
    ¬(42=14 ∧ c.val=14) →
    0 < min (baseRat (1/(42:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(42:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(42:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(42:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(42:ℚ))*logLoRat 42+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate : ∀ d c : Fin 43, 3 ≤ d.val → 3 ≤ c.val →
    ¬(d.val=14 ∧ c.val=14) →
    0 < min (baseRat (1/(d.val:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(d.val:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(d.val:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(d.val:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(d.val:ℚ))*logLoRat d.val+(1/(c.val:ℚ))*logLoRat c.val := by
  intro d c hd hc hn
  have hdN : d.val ≤ 42 := by omega
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
  · simpa only [Nat.cast_ofNat] using finite_gate_row_34 c hc hn
  · simpa only [Nat.cast_ofNat] using finite_gate_row_35 c hc hn
  · simpa only [Nat.cast_ofNat] using finite_gate_row_36 c hc hn
  · simpa only [Nat.cast_ofNat] using finite_gate_row_37 c hc hn
  · simpa only [Nat.cast_ofNat] using finite_gate_row_38 c hc hn
  · simpa only [Nat.cast_ofNat] using finite_gate_row_39 c hc hn
  · simpa only [Nat.cast_ofNat] using finite_gate_row_40 c hc hn
  · simpa only [Nat.cast_ofNat] using finite_gate_row_41 c hc hn
  · simpa only [Nat.cast_ofNat] using finite_gate_row_42 c hc hn

theorem finite_strict_nat (d c : ℕ) (hd0 : 3 ≤ d) (hc0 : 3 ≤ c)
    (hdN : d ≤ 42) (hcN : c ≤ 42) (hn : ¬(d=14 ∧ c=14)) :
    0 < edgeCost 14 (cubicAnchor 14) d c := by
  have hdp : 0 < d := by omega
  have hcp : 0 < c := by omega
  have hg := finite_gate ⟨d,by omega⟩ ⟨c,by omega⟩ hd0 hc0 hn
  have h := rational_edge_gate (baseRat (1/(d:ℚ)) (1/(c:ℚ)))
    (slopeRat (1/(d:ℚ)) (1/(c:ℚ))) gammaLoRat gammaHiRat
    (1/(d:ℚ)) (1/(c:ℚ)) (logLoRat d) (logLoRat c)
    (gamma 14) (log (14/(d:ℝ))) (log (14/(c:ℝ)))
    (by positivity) (by positivity) gamma_rat_bounds.1 gamma_rat_bounds.2
    (degree_log_lower d hd0 hdN) (degree_log_lower c hc0 hcN) hg
  have hm := model_rational (1/(d:ℚ)) (1/(c:ℚ))
  push_cast at h hm
  rw [edge_value_model d c (by positivity) (by positivity), hm]
  exact h

theorem finite_strict (d c : ℤ) (hd0 : 3 ≤ d) (hc0 : 3 ≤ c)
    (hdN : d ≤ 42) (hcN : c ≤ 42) (hn : ¬(d=14 ∧ c=14)) :
    0 < edgeCost 14 (cubicAnchor 14) d c := by
  have hd : (d.toNat:ℤ) = d := Int.toNat_of_nonneg (by omega)
  have hc : (c.toNat:ℤ) = c := Int.toNat_of_nonneg (by omega)
  have h := finite_strict_nat d.toNat c.toNat (by omega) (by omega) (by omega) (by omega)
    (by intro hh; apply hn; constructor <;> omega)
  rw [← hd, ← hc]
  simpa only [Int.cast_natCast] using h

end SparseComponent.TotalFamily.Density14
