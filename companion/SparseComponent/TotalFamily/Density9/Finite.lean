import SparseComponent.TotalFamily.Density9.LogBounds
import SparseComponent.TotalFamily.FiniteCertificateTools

namespace SparseComponent.TotalFamily.Density9
open Finset Matrix Real TotalOnes
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

noncomputable def poly (x y : ℝ) : ℝ :=
  (((0:ℝ)/1)+((-6561:ℝ)/2)*gamma 9)*x^3*y^1 +
  (((0:ℝ)/1)+((-59049:ℝ)/25)*gamma 9)*x^3*y^0 +
  (((0:ℝ)/1)+((39366:ℝ)/5)*gamma 9)*x^2*y^1 +
  (((0:ℝ)/1)+((-8748:ℝ)/25)*gamma 9)*x^2*y^0 +
  (((0:ℝ)/1)+((-6561:ℝ)/2)*gamma 9)*x^1*y^3 +
  (((0:ℝ)/1)+((39366:ℝ)/5)*gamma 9)*x^1*y^2 +
  (((-81:ℝ)/8)+((-648:ℝ)/5)*gamma 9)*x^1*y^1 +
  (((1:ℝ)/8)+((-2349:ℝ)/25)*gamma 9)*x^1*y^0 +
  (((0:ℝ)/1)+((-59049:ℝ)/25)*gamma 9)*x^0*y^3 +
  (((0:ℝ)/1)+((-8748:ℝ)/25)*gamma 9)*x^0*y^2 +
  (((1:ℝ)/8)+((-2349:ℝ)/25)*gamma 9)*x^0*y^1 +
  (((7:ℝ)/72)+((17:ℝ)/1)*gamma 9)*x^0*y^0

theorem poly_identity (x y : ℝ) : polynomialModel 9 (linearAnchor 9) x y = poly x y := by
  unfold polynomialModel linearAnchor poly
  generalize gamma 9 = g
  norm_num
  ring

theorem edge_value (d c : ℝ) (hd : d ≠ 0) (hc : c ≠ 0) :
    edgeCost 9 (linearAnchor 9) d c = poly (1/d) (1/c)+(1/d)*log (9/d)+(1/c)*log (9/c) := by
  have h := edgeCost_reciprocal 9 (1/d) (1/c) (by norm_num) (one_div_ne_zero hd) (one_div_ne_zero hc) (linearAnchor 9)
  simp only [one_div_one_div] at h
  rw [h, polynomial_edge_identity 9 (1/d) (1/c) (by norm_num), poly_identity]
  simp only [div_eq_mul_inv, one_mul]

theorem edge_value_model (d c : ℝ) (hd : d ≠ 0) (hc : c ≠ 0) :
    edgeCost 9 (linearAnchor 9) d c = polynomialModel 9 (linearAnchor 9) (1/d) (1/c)+(1/d)*log (9/d)+(1/c)*log (9/c) := by
  rw [edge_value d c hd hc, poly_identity]

def anchorRat (z : ℚ) : ℚ := 2/(5*9)+(3/5)*z
def baseRat (x y : ℚ) : ℚ := 2/9-1/(9-1)+(x+y)/(9-1)-9^2/(9-1)*x*y
def slopeRat (x y : ℚ) : ℚ :=
  2*9-1-9^2*(x+y)-2*9^2*(9-1)*x*y +
  9^4*(-x*(anchorRat x)^2-y*(anchorRat y)^2+
    2*x*y*(anchorRat x+anchorRat y)-(x^3*y+x*y^3)/2)
def gammaLoRat : ℚ := ((127791187:ℚ)/100000000000)
def gammaHiRat : ℚ := ((31947797:ℚ)/25000000000)
def logLoRat : ℕ → ℚ
  | 2 => ((150407739:ℚ)/100000000)
  | 3 => ((27465307:ℚ)/25000000)
  | 4 => ((81093021:ℚ)/100000000)
  | 5 => ((29389333:ℚ)/50000000)
  | 6 => ((4054651:ℚ)/10000000)
  | 7 => ((12565721:ℚ)/50000000)
  | 8 => ((11778303:ℚ)/100000000)
  | 9 => ((0:ℚ)/1)
  | 10 => ((-2634013:ℚ)/25000000)
  | 11 => ((-2006707:ℚ)/10000000)
  | 12 => ((-1798013:ℚ)/6250000)
  | 13 => ((-36772479:ℚ)/100000000)
  | 14 => ((-11045819:ℚ)/25000000)
  | 15 => ((-51082563:ℚ)/100000000)
  | 16 => ((-11507283:ℚ)/20000000)
  | 17 => ((-63598877:ℚ)/100000000)
  | 18 => ((-69314719:ℚ)/100000000)
  | 19 => ((-74721441:ℚ)/100000000)
  | 20 => ((-7985077:ℚ)/10000000)
  | 21 => ((-84729787:ℚ)/100000000)
  | 22 => ((-22345447:ℚ)/25000000)
  | 23 => ((-23456741:ℚ)/25000000)
  | 24 => ((-49041463:ℚ)/50000000)
  | 25 => ((-817321:ℚ)/800000)
  | 26 => ((-106087197:ℚ)/100000000)
  | 27 => ((-109861229:ℚ)/100000000)
  | _ => 0

theorem model_rational (x y : ℚ) :
    polynomialModel 9 (linearAnchor 9) (x:ℝ) (y:ℝ) = (baseRat x y:ℝ)+(slopeRat x y:ℝ)*gamma 9 := by
  unfold polynomialModel linearAnchor baseRat slopeRat anchorRat
  generalize gamma 9 = g
  push_cast
  norm_num
  ring

theorem gamma_rat_bounds : (gammaLoRat:ℝ) ≤ gamma 9 ∧ gamma 9 ≤ (gammaHiRat:ℝ) := by
  norm_num only [gammaLoRat, gammaHiRat, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg]
  exact gamma_bounds

theorem degree_log_lower (d : ℕ) (hd : 2 ≤ d) (hD : d ≤ 27) :
    (logLoRat d:ℝ) ≤ log (9/(d:ℝ)) := by
  interval_cases d
  · convert ratio_log_lower_2 using 1 <;> norm_num [logLoRat]
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

/-- The finite rational table is checked by kernel reduction; no native evaluator is trusted. -/
theorem finite_gate_row_2 : ∀ c : Fin 28, 2 ≤ c.val →
    ¬(2=9 ∧ c.val=9) →
    0 < min (baseRat (1/(2:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(2:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(2:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(2:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(2:ℚ))*logLoRat 2+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_3 : ∀ c : Fin 28, 2 ≤ c.val →
    ¬(3=9 ∧ c.val=9) →
    0 < min (baseRat (1/(3:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(3:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(3:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(3:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(3:ℚ))*logLoRat 3+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_4 : ∀ c : Fin 28, 2 ≤ c.val →
    ¬(4=9 ∧ c.val=9) →
    0 < min (baseRat (1/(4:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(4:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(4:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(4:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(4:ℚ))*logLoRat 4+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_5 : ∀ c : Fin 28, 2 ≤ c.val →
    ¬(5=9 ∧ c.val=9) →
    0 < min (baseRat (1/(5:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(5:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(5:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(5:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(5:ℚ))*logLoRat 5+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_6 : ∀ c : Fin 28, 2 ≤ c.val →
    ¬(6=9 ∧ c.val=9) →
    0 < min (baseRat (1/(6:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(6:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(6:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(6:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(6:ℚ))*logLoRat 6+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_7 : ∀ c : Fin 28, 2 ≤ c.val →
    ¬(7=9 ∧ c.val=9) →
    0 < min (baseRat (1/(7:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(7:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(7:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(7:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(7:ℚ))*logLoRat 7+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_8 : ∀ c : Fin 28, 2 ≤ c.val →
    ¬(8=9 ∧ c.val=9) →
    0 < min (baseRat (1/(8:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(8:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(8:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(8:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(8:ℚ))*logLoRat 8+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_9 : ∀ c : Fin 28, 2 ≤ c.val →
    ¬(9=9 ∧ c.val=9) →
    0 < min (baseRat (1/(9:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(9:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(9:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(9:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(9:ℚ))*logLoRat 9+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_10 : ∀ c : Fin 28, 2 ≤ c.val →
    ¬(10=9 ∧ c.val=9) →
    0 < min (baseRat (1/(10:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(10:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(10:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(10:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(10:ℚ))*logLoRat 10+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_11 : ∀ c : Fin 28, 2 ≤ c.val →
    ¬(11=9 ∧ c.val=9) →
    0 < min (baseRat (1/(11:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(11:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(11:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(11:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(11:ℚ))*logLoRat 11+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_12 : ∀ c : Fin 28, 2 ≤ c.val →
    ¬(12=9 ∧ c.val=9) →
    0 < min (baseRat (1/(12:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(12:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(12:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(12:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(12:ℚ))*logLoRat 12+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_13 : ∀ c : Fin 28, 2 ≤ c.val →
    ¬(13=9 ∧ c.val=9) →
    0 < min (baseRat (1/(13:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(13:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(13:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(13:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(13:ℚ))*logLoRat 13+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_14 : ∀ c : Fin 28, 2 ≤ c.val →
    ¬(14=9 ∧ c.val=9) →
    0 < min (baseRat (1/(14:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(14:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(14:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(14:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(14:ℚ))*logLoRat 14+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_15 : ∀ c : Fin 28, 2 ≤ c.val →
    ¬(15=9 ∧ c.val=9) →
    0 < min (baseRat (1/(15:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(15:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(15:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(15:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(15:ℚ))*logLoRat 15+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_16 : ∀ c : Fin 28, 2 ≤ c.val →
    ¬(16=9 ∧ c.val=9) →
    0 < min (baseRat (1/(16:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(16:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(16:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(16:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(16:ℚ))*logLoRat 16+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_17 : ∀ c : Fin 28, 2 ≤ c.val →
    ¬(17=9 ∧ c.val=9) →
    0 < min (baseRat (1/(17:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(17:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(17:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(17:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(17:ℚ))*logLoRat 17+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_18 : ∀ c : Fin 28, 2 ≤ c.val →
    ¬(18=9 ∧ c.val=9) →
    0 < min (baseRat (1/(18:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(18:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(18:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(18:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(18:ℚ))*logLoRat 18+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_19 : ∀ c : Fin 28, 2 ≤ c.val →
    ¬(19=9 ∧ c.val=9) →
    0 < min (baseRat (1/(19:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(19:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(19:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(19:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(19:ℚ))*logLoRat 19+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_20 : ∀ c : Fin 28, 2 ≤ c.val →
    ¬(20=9 ∧ c.val=9) →
    0 < min (baseRat (1/(20:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(20:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(20:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(20:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(20:ℚ))*logLoRat 20+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_21 : ∀ c : Fin 28, 2 ≤ c.val →
    ¬(21=9 ∧ c.val=9) →
    0 < min (baseRat (1/(21:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(21:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(21:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(21:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(21:ℚ))*logLoRat 21+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_22 : ∀ c : Fin 28, 2 ≤ c.val →
    ¬(22=9 ∧ c.val=9) →
    0 < min (baseRat (1/(22:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(22:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(22:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(22:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(22:ℚ))*logLoRat 22+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_23 : ∀ c : Fin 28, 2 ≤ c.val →
    ¬(23=9 ∧ c.val=9) →
    0 < min (baseRat (1/(23:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(23:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(23:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(23:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(23:ℚ))*logLoRat 23+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_24 : ∀ c : Fin 28, 2 ≤ c.val →
    ¬(24=9 ∧ c.val=9) →
    0 < min (baseRat (1/(24:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(24:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(24:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(24:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(24:ℚ))*logLoRat 24+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_25 : ∀ c : Fin 28, 2 ≤ c.val →
    ¬(25=9 ∧ c.val=9) →
    0 < min (baseRat (1/(25:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(25:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(25:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(25:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(25:ℚ))*logLoRat 25+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_26 : ∀ c : Fin 28, 2 ≤ c.val →
    ¬(26=9 ∧ c.val=9) →
    0 < min (baseRat (1/(26:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(26:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(26:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(26:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(26:ℚ))*logLoRat 26+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_27 : ∀ c : Fin 28, 2 ≤ c.val →
    ¬(27=9 ∧ c.val=9) →
    0 < min (baseRat (1/(27:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(27:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(27:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(27:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(27:ℚ))*logLoRat 27+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate : ∀ d c : Fin 28, 2 ≤ d.val → 2 ≤ c.val →
    ¬(d.val=9 ∧ c.val=9) →
    0 < min (baseRat (1/(d.val:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(d.val:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(d.val:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(d.val:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(d.val:ℚ))*logLoRat d.val+(1/(c.val:ℚ))*logLoRat c.val := by
  intro d c hd hc hn
  have hdN : d.val ≤ 27 := by omega
  generalize hk : d.val = k at hd hdN hn ⊢
  interval_cases k
  · simpa only [Nat.cast_ofNat] using finite_gate_row_2 c hc hn
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

theorem finite_strict_nat (d c : ℕ) (hd0 : 2 ≤ d) (hc0 : 2 ≤ c)
    (hdN : d ≤ 27) (hcN : c ≤ 27) (hn : ¬(d=9 ∧ c=9)) :
    0 < edgeCost 9 (linearAnchor 9) d c := by
  have hdp : 0 < d := by omega
  have hcp : 0 < c := by omega
  have hg := finite_gate ⟨d,by omega⟩ ⟨c,by omega⟩ hd0 hc0 hn
  have h := rational_edge_gate (baseRat (1/(d:ℚ)) (1/(c:ℚ)))
    (slopeRat (1/(d:ℚ)) (1/(c:ℚ))) gammaLoRat gammaHiRat
    (1/(d:ℚ)) (1/(c:ℚ)) (logLoRat d) (logLoRat c)
    (gamma 9) (log (9/(d:ℝ))) (log (9/(c:ℝ)))
    (by positivity) (by positivity) gamma_rat_bounds.1 gamma_rat_bounds.2
    (degree_log_lower d hd0 hdN) (degree_log_lower c hc0 hcN) hg
  have hm := model_rational (1/(d:ℚ)) (1/(c:ℚ))
  push_cast at h hm
  rw [edge_value_model d c (by positivity) (by positivity), hm]
  exact h

theorem finite_strict (d c : ℤ) (hd0 : 2 ≤ d) (hc0 : 2 ≤ c)
    (hdN : d ≤ 27) (hcN : c ≤ 27) (hn : ¬(d=9 ∧ c=9)) :
    0 < edgeCost 9 (linearAnchor 9) d c := by
  have hd : (d.toNat:ℤ) = d := Int.toNat_of_nonneg (by omega)
  have hc : (c.toNat:ℤ) = c := Int.toNat_of_nonneg (by omega)
  have h := finite_strict_nat d.toNat c.toNat (by omega) (by omega) (by omega) (by omega)
    (by intro hh; apply hn; constructor <;> omega)
  rw [← hd, ← hc]
  simpa only [Int.cast_natCast] using h

end SparseComponent.TotalFamily.Density9
