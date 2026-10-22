import SparseComponent.TotalFamily.Density13.LogBounds
import SparseComponent.TotalFamily.FiniteCertificateTools

namespace SparseComponent.TotalFamily.Density13
open Finset Matrix Real TotalOnes
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

noncomputable def poly (x y : ℝ) : ℝ :=
  (((0:ℝ)/1)+((-257049:ℝ)/4)*gamma 13)*x^7*y^0 +
  (((0:ℝ)/1)+((-54925:ℝ)/2)*gamma 13)*x^6*y^0 +
  (((0:ℝ)/1)+((3213197:ℝ)/36)*gamma 13)*x^5*y^0 +
  (((0:ℝ)/1)+((-85683:ℝ)/1)*gamma 13)*x^4*y^1 +
  (((0:ℝ)/1)+((174772:ℝ)/9)*gamma 13)*x^4*y^0 +
  (((0:ℝ)/1)+((-195533:ℝ)/6)*gamma 13)*x^3*y^1 +
  (((0:ℝ)/1)+((-397477:ℝ)/12)*gamma 13)*x^3*y^0 +
  (((0:ℝ)/1)+((184379:ℝ)/3)*gamma 13)*x^2*y^1 +
  (((0:ℝ)/1)+((46913:ℝ)/234)*gamma 13)*x^2*y^0 +
  (((0:ℝ)/1)+((-85683:ℝ)/1)*gamma 13)*x^1*y^4 +
  (((0:ℝ)/1)+((-195533:ℝ)/6)*gamma 13)*x^1*y^3 +
  (((0:ℝ)/1)+((184379:ℝ)/3)*gamma 13)*x^1*y^2 +
  (((-169:ℝ)/12)+((-13286:ℝ)/3)*gamma 13)*x^1*y^1 +
  (((1:ℝ)/12)+((-1030045:ℝ)/6084)*gamma 13)*x^1*y^0 +
  (((0:ℝ)/1)+((-257049:ℝ)/4)*gamma 13)*x^0*y^7 +
  (((0:ℝ)/1)+((-54925:ℝ)/2)*gamma 13)*x^0*y^6 +
  (((0:ℝ)/1)+((3213197:ℝ)/36)*gamma 13)*x^0*y^5 +
  (((0:ℝ)/1)+((174772:ℝ)/9)*gamma 13)*x^0*y^4 +
  (((0:ℝ)/1)+((-397477:ℝ)/12)*gamma 13)*x^0*y^3 +
  (((0:ℝ)/1)+((46913:ℝ)/234)*gamma 13)*x^0*y^2 +
  (((1:ℝ)/12)+((-1030045:ℝ)/6084)*gamma 13)*x^0*y^1 +
  (((11:ℝ)/156)+((25:ℝ)/1)*gamma 13)*x^0*y^0

theorem poly_identity (x y : ℝ) : polynomialModel 13 (cubicAnchor 13) x y = poly x y := by
  unfold polynomialModel cubicAnchor poly
  generalize gamma 13 = g
  norm_num
  ring

theorem edge_value (d c : ℝ) (hd : d ≠ 0) (hc : c ≠ 0) :
    edgeCost 13 (cubicAnchor 13) d c = poly (1/d) (1/c)+(1/d)*log (13/d)+(1/c)*log (13/c) := by
  have h := edgeCost_reciprocal 13 (1/d) (1/c) (by norm_num) (one_div_ne_zero hd) (one_div_ne_zero hc) (cubicAnchor 13)
  simp only [one_div_one_div] at h
  rw [h, polynomial_edge_identity 13 (1/d) (1/c) (by norm_num), poly_identity]
  simp only [div_eq_mul_inv, one_mul]

theorem edge_value_model (d c : ℝ) (hd : d ≠ 0) (hc : c ≠ 0) :
    edgeCost 13 (cubicAnchor 13) d c = polynomialModel 13 (cubicAnchor 13) (1/d) (1/c)+(1/d)*log (13/d)+(1/c)*log (13/c) := by
  rw [edge_value d c hd hc, poly_identity]

def anchorRat (z : ℚ) : ℚ := z-(2/3)*(z-1/13)^2-(3/2)*(z-1/13)^3
def baseRat (x y : ℚ) : ℚ := 2/13-1/(13-1)+(x+y)/(13-1)-13^2/(13-1)*x*y
def slopeRat (x y : ℚ) : ℚ :=
  2*13-1-13^2*(x+y)-2*13^2*(13-1)*x*y +
  13^4*(-x*(anchorRat x)^2-y*(anchorRat y)^2+
    2*x*y*(anchorRat x+anchorRat y)-(x^3*y+x*y^3)/2)
def gammaLoRat : ℚ := ((42347929:ℚ)/100000000000)
def gammaHiRat : ℚ := ((42347931:ℚ)/100000000000)
def logLoRat : ℕ → ℚ
  | 3 => ((73316853:ℚ)/50000000)
  | 4 => ((117865499:ℚ)/100000000)
  | 5 => ((11943893:ℚ)/12500000)
  | 6 => ((19329747:ℚ)/25000000)
  | 7 => ((773799:ℚ)/1250000)
  | 8 => ((48550781:ℚ)/100000000)
  | 9 => ((18386239:ℚ)/50000000)
  | 10 => ((13118213:ℚ)/50000000)
  | 11 => ((130511:ℚ)/781250)
  | 12 => ((800427:ℚ)/10000000)
  | 13 => ((0:ℚ)/1)
  | 14 => ((-3705399:ℚ)/50000000)
  | 15 => ((-2862017:ℚ)/20000000)
  | 16 => ((-20763937:ℚ)/100000000)
  | 17 => ((-26826399:ℚ)/100000000)
  | 18 => ((-32542241:ℚ)/100000000)
  | 19 => ((-37948963:ℚ)/100000000)
  | 20 => ((-10769573:ℚ)/25000000)
  | 21 => ((-47957309:ℚ)/100000000)
  | 22 => ((-5260931:ℚ)/10000000)
  | 23 => ((-28527243:ℚ)/50000000)
  | 24 => ((-3831903:ℚ)/6250000)
  | 25 => ((-65392647:ℚ)/100000000)
  | 26 => ((-69314719:ℚ)/100000000)
  | 27 => ((-73088751:ℚ)/100000000)
  | 28 => ((-19181379:ℚ)/25000000)
  | 29 => ((-10029331:ℚ)/12500000)
  | 30 => ((-83624803:ℚ)/100000000)
  | 31 => ((-17380757:ℚ)/20000000)
  | 32 => ((-18015731:ℚ)/20000000)
  | 33 => ((-93155821:ℚ)/100000000)
  | 34 => ((-96141117:ℚ)/100000000)
  | 35 => ((-99039871:ℚ)/100000000)
  | 36 => ((-101856959:ℚ)/100000000)
  | 37 => ((-13074607:ℚ)/12500000)
  | 38 => ((-107263681:ℚ)/100000000)
  | 39 => ((-109861229:ℚ)/100000000)
  | _ => 0

theorem model_rational (x y : ℚ) :
    polynomialModel 13 (cubicAnchor 13) (x:ℝ) (y:ℝ) = (baseRat x y:ℝ)+(slopeRat x y:ℝ)*gamma 13 := by
  unfold polynomialModel cubicAnchor baseRat slopeRat anchorRat
  generalize gamma 13 = g
  push_cast
  norm_num
  ring

theorem gamma_rat_bounds : (gammaLoRat:ℝ) ≤ gamma 13 ∧ gamma 13 ≤ (gammaHiRat:ℝ) := by
  norm_num only [gammaLoRat, gammaHiRat, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg]
  exact gamma_bounds

theorem degree_log_lower (d : ℕ) (hd : 3 ≤ d) (hD : d ≤ 39) :
    (logLoRat d:ℝ) ≤ log (13/(d:ℝ)) := by
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

/-- The finite rational table is checked by kernel reduction; no native evaluator is trusted. -/
theorem finite_gate_row_3 : ∀ c : Fin 40, 3 ≤ c.val →
    ¬(3=13 ∧ c.val=13) →
    0 < min (baseRat (1/(3:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(3:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(3:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(3:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(3:ℚ))*logLoRat 3+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_4 : ∀ c : Fin 40, 3 ≤ c.val →
    ¬(4=13 ∧ c.val=13) →
    0 < min (baseRat (1/(4:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(4:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(4:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(4:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(4:ℚ))*logLoRat 4+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_5 : ∀ c : Fin 40, 3 ≤ c.val →
    ¬(5=13 ∧ c.val=13) →
    0 < min (baseRat (1/(5:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(5:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(5:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(5:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(5:ℚ))*logLoRat 5+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_6 : ∀ c : Fin 40, 3 ≤ c.val →
    ¬(6=13 ∧ c.val=13) →
    0 < min (baseRat (1/(6:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(6:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(6:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(6:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(6:ℚ))*logLoRat 6+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_7 : ∀ c : Fin 40, 3 ≤ c.val →
    ¬(7=13 ∧ c.val=13) →
    0 < min (baseRat (1/(7:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(7:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(7:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(7:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(7:ℚ))*logLoRat 7+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_8 : ∀ c : Fin 40, 3 ≤ c.val →
    ¬(8=13 ∧ c.val=13) →
    0 < min (baseRat (1/(8:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(8:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(8:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(8:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(8:ℚ))*logLoRat 8+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_9 : ∀ c : Fin 40, 3 ≤ c.val →
    ¬(9=13 ∧ c.val=13) →
    0 < min (baseRat (1/(9:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(9:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(9:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(9:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(9:ℚ))*logLoRat 9+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_10 : ∀ c : Fin 40, 3 ≤ c.val →
    ¬(10=13 ∧ c.val=13) →
    0 < min (baseRat (1/(10:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(10:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(10:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(10:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(10:ℚ))*logLoRat 10+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_11 : ∀ c : Fin 40, 3 ≤ c.val →
    ¬(11=13 ∧ c.val=13) →
    0 < min (baseRat (1/(11:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(11:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(11:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(11:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(11:ℚ))*logLoRat 11+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_12 : ∀ c : Fin 40, 3 ≤ c.val →
    ¬(12=13 ∧ c.val=13) →
    0 < min (baseRat (1/(12:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(12:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(12:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(12:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(12:ℚ))*logLoRat 12+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_13 : ∀ c : Fin 40, 3 ≤ c.val →
    ¬(13=13 ∧ c.val=13) →
    0 < min (baseRat (1/(13:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(13:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(13:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(13:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(13:ℚ))*logLoRat 13+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_14 : ∀ c : Fin 40, 3 ≤ c.val →
    ¬(14=13 ∧ c.val=13) →
    0 < min (baseRat (1/(14:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(14:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(14:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(14:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(14:ℚ))*logLoRat 14+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_15 : ∀ c : Fin 40, 3 ≤ c.val →
    ¬(15=13 ∧ c.val=13) →
    0 < min (baseRat (1/(15:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(15:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(15:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(15:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(15:ℚ))*logLoRat 15+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_16 : ∀ c : Fin 40, 3 ≤ c.val →
    ¬(16=13 ∧ c.val=13) →
    0 < min (baseRat (1/(16:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(16:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(16:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(16:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(16:ℚ))*logLoRat 16+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_17 : ∀ c : Fin 40, 3 ≤ c.val →
    ¬(17=13 ∧ c.val=13) →
    0 < min (baseRat (1/(17:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(17:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(17:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(17:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(17:ℚ))*logLoRat 17+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_18 : ∀ c : Fin 40, 3 ≤ c.val →
    ¬(18=13 ∧ c.val=13) →
    0 < min (baseRat (1/(18:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(18:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(18:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(18:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(18:ℚ))*logLoRat 18+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_19 : ∀ c : Fin 40, 3 ≤ c.val →
    ¬(19=13 ∧ c.val=13) →
    0 < min (baseRat (1/(19:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(19:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(19:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(19:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(19:ℚ))*logLoRat 19+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_20 : ∀ c : Fin 40, 3 ≤ c.val →
    ¬(20=13 ∧ c.val=13) →
    0 < min (baseRat (1/(20:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(20:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(20:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(20:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(20:ℚ))*logLoRat 20+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_21 : ∀ c : Fin 40, 3 ≤ c.val →
    ¬(21=13 ∧ c.val=13) →
    0 < min (baseRat (1/(21:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(21:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(21:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(21:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(21:ℚ))*logLoRat 21+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_22 : ∀ c : Fin 40, 3 ≤ c.val →
    ¬(22=13 ∧ c.val=13) →
    0 < min (baseRat (1/(22:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(22:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(22:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(22:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(22:ℚ))*logLoRat 22+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_23 : ∀ c : Fin 40, 3 ≤ c.val →
    ¬(23=13 ∧ c.val=13) →
    0 < min (baseRat (1/(23:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(23:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(23:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(23:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(23:ℚ))*logLoRat 23+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_24 : ∀ c : Fin 40, 3 ≤ c.val →
    ¬(24=13 ∧ c.val=13) →
    0 < min (baseRat (1/(24:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(24:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(24:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(24:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(24:ℚ))*logLoRat 24+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_25 : ∀ c : Fin 40, 3 ≤ c.val →
    ¬(25=13 ∧ c.val=13) →
    0 < min (baseRat (1/(25:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(25:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(25:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(25:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(25:ℚ))*logLoRat 25+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_26 : ∀ c : Fin 40, 3 ≤ c.val →
    ¬(26=13 ∧ c.val=13) →
    0 < min (baseRat (1/(26:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(26:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(26:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(26:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(26:ℚ))*logLoRat 26+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_27 : ∀ c : Fin 40, 3 ≤ c.val →
    ¬(27=13 ∧ c.val=13) →
    0 < min (baseRat (1/(27:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(27:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(27:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(27:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(27:ℚ))*logLoRat 27+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_28 : ∀ c : Fin 40, 3 ≤ c.val →
    ¬(28=13 ∧ c.val=13) →
    0 < min (baseRat (1/(28:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(28:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(28:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(28:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(28:ℚ))*logLoRat 28+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_29 : ∀ c : Fin 40, 3 ≤ c.val →
    ¬(29=13 ∧ c.val=13) →
    0 < min (baseRat (1/(29:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(29:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(29:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(29:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(29:ℚ))*logLoRat 29+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_30 : ∀ c : Fin 40, 3 ≤ c.val →
    ¬(30=13 ∧ c.val=13) →
    0 < min (baseRat (1/(30:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(30:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(30:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(30:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(30:ℚ))*logLoRat 30+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_31 : ∀ c : Fin 40, 3 ≤ c.val →
    ¬(31=13 ∧ c.val=13) →
    0 < min (baseRat (1/(31:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(31:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(31:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(31:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(31:ℚ))*logLoRat 31+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_32 : ∀ c : Fin 40, 3 ≤ c.val →
    ¬(32=13 ∧ c.val=13) →
    0 < min (baseRat (1/(32:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(32:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(32:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(32:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(32:ℚ))*logLoRat 32+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_33 : ∀ c : Fin 40, 3 ≤ c.val →
    ¬(33=13 ∧ c.val=13) →
    0 < min (baseRat (1/(33:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(33:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(33:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(33:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(33:ℚ))*logLoRat 33+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_34 : ∀ c : Fin 40, 3 ≤ c.val →
    ¬(34=13 ∧ c.val=13) →
    0 < min (baseRat (1/(34:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(34:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(34:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(34:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(34:ℚ))*logLoRat 34+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_35 : ∀ c : Fin 40, 3 ≤ c.val →
    ¬(35=13 ∧ c.val=13) →
    0 < min (baseRat (1/(35:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(35:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(35:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(35:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(35:ℚ))*logLoRat 35+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_36 : ∀ c : Fin 40, 3 ≤ c.val →
    ¬(36=13 ∧ c.val=13) →
    0 < min (baseRat (1/(36:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(36:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(36:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(36:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(36:ℚ))*logLoRat 36+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_37 : ∀ c : Fin 40, 3 ≤ c.val →
    ¬(37=13 ∧ c.val=13) →
    0 < min (baseRat (1/(37:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(37:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(37:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(37:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(37:ℚ))*logLoRat 37+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_38 : ∀ c : Fin 40, 3 ≤ c.val →
    ¬(38=13 ∧ c.val=13) →
    0 < min (baseRat (1/(38:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(38:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(38:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(38:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(38:ℚ))*logLoRat 38+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_39 : ∀ c : Fin 40, 3 ≤ c.val →
    ¬(39=13 ∧ c.val=13) →
    0 < min (baseRat (1/(39:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(39:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(39:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(39:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(39:ℚ))*logLoRat 39+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate : ∀ d c : Fin 40, 3 ≤ d.val → 3 ≤ c.val →
    ¬(d.val=13 ∧ c.val=13) →
    0 < min (baseRat (1/(d.val:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(d.val:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(d.val:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(d.val:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(d.val:ℚ))*logLoRat d.val+(1/(c.val:ℚ))*logLoRat c.val := by
  intro d c hd hc hn
  have hdN : d.val ≤ 39 := by omega
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

theorem finite_strict_nat (d c : ℕ) (hd0 : 3 ≤ d) (hc0 : 3 ≤ c)
    (hdN : d ≤ 39) (hcN : c ≤ 39) (hn : ¬(d=13 ∧ c=13)) :
    0 < edgeCost 13 (cubicAnchor 13) d c := by
  have hdp : 0 < d := by omega
  have hcp : 0 < c := by omega
  have hg := finite_gate ⟨d,by omega⟩ ⟨c,by omega⟩ hd0 hc0 hn
  have h := rational_edge_gate (baseRat (1/(d:ℚ)) (1/(c:ℚ)))
    (slopeRat (1/(d:ℚ)) (1/(c:ℚ))) gammaLoRat gammaHiRat
    (1/(d:ℚ)) (1/(c:ℚ)) (logLoRat d) (logLoRat c)
    (gamma 13) (log (13/(d:ℝ))) (log (13/(c:ℝ)))
    (by positivity) (by positivity) gamma_rat_bounds.1 gamma_rat_bounds.2
    (degree_log_lower d hd0 hdN) (degree_log_lower c hc0 hcN) hg
  have hm := model_rational (1/(d:ℚ)) (1/(c:ℚ))
  push_cast at h hm
  rw [edge_value_model d c (by positivity) (by positivity), hm]
  exact h

theorem finite_strict (d c : ℤ) (hd0 : 3 ≤ d) (hc0 : 3 ≤ c)
    (hdN : d ≤ 39) (hcN : c ≤ 39) (hn : ¬(d=13 ∧ c=13)) :
    0 < edgeCost 13 (cubicAnchor 13) d c := by
  have hd : (d.toNat:ℤ) = d := Int.toNat_of_nonneg (by omega)
  have hc : (c.toNat:ℤ) = c := Int.toNat_of_nonneg (by omega)
  have h := finite_strict_nat d.toNat c.toNat (by omega) (by omega) (by omega) (by omega)
    (by intro hh; apply hn; constructor <;> omega)
  rw [← hd, ← hc]
  simpa only [Int.cast_natCast] using h

end SparseComponent.TotalFamily.Density13
