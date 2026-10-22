import SparseComponent.TotalFamily.Density10.LogBounds
import SparseComponent.TotalFamily.FiniteCertificateTools

namespace SparseComponent.TotalFamily.Density10
open Finset Matrix Real TotalOnes
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

noncomputable def poly (x y : ℝ) : ℝ :=
  (((0:ℝ)/1)+((-10000:ℝ)/1)*gamma 10)*x^5*y^0 +
  (((0:ℝ)/1)+((24000:ℝ)/1)*gamma 10)*x^4*y^0 +
  (((0:ℝ)/1)+((-25000:ℝ)/1)*gamma 10)*x^3*y^1 +
  (((0:ℝ)/1)+((-14600:ℝ)/1)*gamma 10)*x^3*y^0 +
  (((0:ℝ)/1)+((24000:ℝ)/1)*gamma 10)*x^2*y^1 +
  (((0:ℝ)/1)+((240:ℝ)/1)*gamma 10)*x^2*y^0 +
  (((0:ℝ)/1)+((-25000:ℝ)/1)*gamma 10)*x^1*y^3 +
  (((0:ℝ)/1)+((24000:ℝ)/1)*gamma 10)*x^1*y^2 +
  (((-100:ℝ)/9)+((-2200:ℝ)/1)*gamma 10)*x^1*y^1 +
  (((1:ℝ)/9)+((-101:ℝ)/1)*gamma 10)*x^1*y^0 +
  (((0:ℝ)/1)+((-10000:ℝ)/1)*gamma 10)*x^0*y^5 +
  (((0:ℝ)/1)+((24000:ℝ)/1)*gamma 10)*x^0*y^4 +
  (((0:ℝ)/1)+((-14600:ℝ)/1)*gamma 10)*x^0*y^3 +
  (((0:ℝ)/1)+((240:ℝ)/1)*gamma 10)*x^0*y^2 +
  (((1:ℝ)/9)+((-101:ℝ)/1)*gamma 10)*x^0*y^1 +
  (((4:ℝ)/45)+((19:ℝ)/1)*gamma 10)*x^0*y^0

theorem poly_identity (x y : ℝ) : polynomialModel 10 quadraticAnchor x y = poly x y := by
  unfold polynomialModel quadraticAnchor poly
  generalize gamma 10 = g
  norm_num
  ring

theorem edge_value (d c : ℝ) (hd : d ≠ 0) (hc : c ≠ 0) :
    edgeCost 10 quadraticAnchor d c = poly (1/d) (1/c)+(1/d)*log (10/d)+(1/c)*log (10/c) := by
  have h := edgeCost_reciprocal 10 (1/d) (1/c) (by norm_num) (one_div_ne_zero hd) (one_div_ne_zero hc) quadraticAnchor
  simp only [one_div_one_div] at h
  rw [h, polynomial_edge_identity 10 (1/d) (1/c) (by norm_num), poly_identity]
  simp only [div_eq_mul_inv, one_mul]

theorem edge_value_model (d c : ℝ) (hd : d ≠ 0) (hc : c ≠ 0) :
    edgeCost 10 quadraticAnchor d c = polynomialModel 10 quadraticAnchor (1/d) (1/c)+(1/d)*log (10/d)+(1/c)*log (10/c) := by
  rw [edge_value d c hd hc, poly_identity]

def anchorRat (z : ℚ) : ℚ := -1/100+(6/5)*z-z^2
def baseRat (x y : ℚ) : ℚ := 2/10-1/(10-1)+(x+y)/(10-1)-10^2/(10-1)*x*y
def slopeRat (x y : ℚ) : ℚ :=
  2*10-1-10^2*(x+y)-2*10^2*(10-1)*x*y +
  10^4*(-x*(anchorRat x)^2-y*(anchorRat y)^2+
    2*x*y*(anchorRat x+anchorRat y)-(x^3*y+x*y^3)/2)
def gammaLoRat : ℚ := ((18604433:ℚ)/20000000000)
def gammaHiRat : ℚ := ((46511083:ℚ)/50000000000)
def logLoRat : ℕ → ℚ
  | 2 => ((160943791:ℚ)/100000000)
  | 3 => ((752483:ℚ)/625000)
  | 4 => ((91629073:ℚ)/100000000)
  | 5 => ((34657359:ℚ)/50000000)
  | 6 => ((25541281:ℚ)/50000000)
  | 7 => ((17833747:ℚ)/50000000)
  | 8 => ((4462871:ℚ)/20000000)
  | 9 => ((10536051:ℚ)/100000000)
  | 10 => ((0:ℚ)/1)
  | 11 => ((-4765509:ℚ)/50000000)
  | 12 => ((-4558039:ℚ)/25000000)
  | 13 => ((-26236427:ℚ)/100000000)
  | 14 => ((-4205903:ℚ)/12500000)
  | 15 => ((-40546511:ℚ)/100000000)
  | 16 => ((-47000363:ℚ)/100000000)
  | 17 => ((-26531413:ℚ)/50000000)
  | 18 => ((-58778667:ℚ)/100000000)
  | 19 => ((-64185389:ℚ)/100000000)
  | 20 => ((-69314719:ℚ)/100000000)
  | 21 => ((-14838747:ℚ)/20000000)
  | 22 => ((-78845737:ℚ)/100000000)
  | 23 => ((-83290913:ℚ)/100000000)
  | 24 => ((-43773437:ℚ)/50000000)
  | 25 => ((-45814537:ℚ)/50000000)
  | 26 => ((-19110229:ℚ)/20000000)
  | 27 => ((-49662589:ℚ)/50000000)
  | 28 => ((-51480971:ℚ)/50000000)
  | 29 => ((-53235537:ℚ)/50000000)
  | 30 => ((-109861229:ℚ)/100000000)
  | _ => 0

theorem model_rational (x y : ℚ) :
    polynomialModel 10 quadraticAnchor (x:ℝ) (y:ℝ) = (baseRat x y:ℝ)+(slopeRat x y:ℝ)*gamma 10 := by
  unfold polynomialModel quadraticAnchor baseRat slopeRat anchorRat
  generalize gamma 10 = g
  push_cast
  norm_num
  ring

theorem gamma_rat_bounds : (gammaLoRat:ℝ) ≤ gamma 10 ∧ gamma 10 ≤ (gammaHiRat:ℝ) := by
  norm_num only [gammaLoRat, gammaHiRat, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg]
  exact gamma_bounds

theorem degree_log_lower (d : ℕ) (hd : 2 ≤ d) (hD : d ≤ 30) :
    (logLoRat d:ℝ) ≤ log (10/(d:ℝ)) := by
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
  · convert ratio_log_lower_28 using 1 <;> norm_num [logLoRat]
  · convert ratio_log_lower_29 using 1 <;> norm_num [logLoRat]
  · convert ratio_log_lower_30 using 1 <;> norm_num [logLoRat]

/-- The finite rational table is checked by kernel reduction; no native evaluator is trusted. -/
theorem finite_gate_row_2 : ∀ c : Fin 31, 2 ≤ c.val →
    ¬(2=10 ∧ c.val=10) →
    0 < min (baseRat (1/(2:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(2:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(2:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(2:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(2:ℚ))*logLoRat 2+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_3 : ∀ c : Fin 31, 2 ≤ c.val →
    ¬(3=10 ∧ c.val=10) →
    0 < min (baseRat (1/(3:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(3:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(3:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(3:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(3:ℚ))*logLoRat 3+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_4 : ∀ c : Fin 31, 2 ≤ c.val →
    ¬(4=10 ∧ c.val=10) →
    0 < min (baseRat (1/(4:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(4:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(4:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(4:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(4:ℚ))*logLoRat 4+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_5 : ∀ c : Fin 31, 2 ≤ c.val →
    ¬(5=10 ∧ c.val=10) →
    0 < min (baseRat (1/(5:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(5:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(5:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(5:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(5:ℚ))*logLoRat 5+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_6 : ∀ c : Fin 31, 2 ≤ c.val →
    ¬(6=10 ∧ c.val=10) →
    0 < min (baseRat (1/(6:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(6:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(6:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(6:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(6:ℚ))*logLoRat 6+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_7 : ∀ c : Fin 31, 2 ≤ c.val →
    ¬(7=10 ∧ c.val=10) →
    0 < min (baseRat (1/(7:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(7:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(7:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(7:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(7:ℚ))*logLoRat 7+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_8 : ∀ c : Fin 31, 2 ≤ c.val →
    ¬(8=10 ∧ c.val=10) →
    0 < min (baseRat (1/(8:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(8:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(8:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(8:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(8:ℚ))*logLoRat 8+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_9 : ∀ c : Fin 31, 2 ≤ c.val →
    ¬(9=10 ∧ c.val=10) →
    0 < min (baseRat (1/(9:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(9:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(9:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(9:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(9:ℚ))*logLoRat 9+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_10 : ∀ c : Fin 31, 2 ≤ c.val →
    ¬(10=10 ∧ c.val=10) →
    0 < min (baseRat (1/(10:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(10:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(10:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(10:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(10:ℚ))*logLoRat 10+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_11 : ∀ c : Fin 31, 2 ≤ c.val →
    ¬(11=10 ∧ c.val=10) →
    0 < min (baseRat (1/(11:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(11:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(11:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(11:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(11:ℚ))*logLoRat 11+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_12 : ∀ c : Fin 31, 2 ≤ c.val →
    ¬(12=10 ∧ c.val=10) →
    0 < min (baseRat (1/(12:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(12:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(12:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(12:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(12:ℚ))*logLoRat 12+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_13 : ∀ c : Fin 31, 2 ≤ c.val →
    ¬(13=10 ∧ c.val=10) →
    0 < min (baseRat (1/(13:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(13:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(13:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(13:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(13:ℚ))*logLoRat 13+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_14 : ∀ c : Fin 31, 2 ≤ c.val →
    ¬(14=10 ∧ c.val=10) →
    0 < min (baseRat (1/(14:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(14:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(14:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(14:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(14:ℚ))*logLoRat 14+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_15 : ∀ c : Fin 31, 2 ≤ c.val →
    ¬(15=10 ∧ c.val=10) →
    0 < min (baseRat (1/(15:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(15:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(15:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(15:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(15:ℚ))*logLoRat 15+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_16 : ∀ c : Fin 31, 2 ≤ c.val →
    ¬(16=10 ∧ c.val=10) →
    0 < min (baseRat (1/(16:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(16:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(16:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(16:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(16:ℚ))*logLoRat 16+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_17 : ∀ c : Fin 31, 2 ≤ c.val →
    ¬(17=10 ∧ c.val=10) →
    0 < min (baseRat (1/(17:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(17:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(17:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(17:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(17:ℚ))*logLoRat 17+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_18 : ∀ c : Fin 31, 2 ≤ c.val →
    ¬(18=10 ∧ c.val=10) →
    0 < min (baseRat (1/(18:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(18:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(18:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(18:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(18:ℚ))*logLoRat 18+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_19 : ∀ c : Fin 31, 2 ≤ c.val →
    ¬(19=10 ∧ c.val=10) →
    0 < min (baseRat (1/(19:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(19:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(19:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(19:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(19:ℚ))*logLoRat 19+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_20 : ∀ c : Fin 31, 2 ≤ c.val →
    ¬(20=10 ∧ c.val=10) →
    0 < min (baseRat (1/(20:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(20:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(20:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(20:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(20:ℚ))*logLoRat 20+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_21 : ∀ c : Fin 31, 2 ≤ c.val →
    ¬(21=10 ∧ c.val=10) →
    0 < min (baseRat (1/(21:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(21:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(21:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(21:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(21:ℚ))*logLoRat 21+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_22 : ∀ c : Fin 31, 2 ≤ c.val →
    ¬(22=10 ∧ c.val=10) →
    0 < min (baseRat (1/(22:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(22:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(22:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(22:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(22:ℚ))*logLoRat 22+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_23 : ∀ c : Fin 31, 2 ≤ c.val →
    ¬(23=10 ∧ c.val=10) →
    0 < min (baseRat (1/(23:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(23:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(23:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(23:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(23:ℚ))*logLoRat 23+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_24 : ∀ c : Fin 31, 2 ≤ c.val →
    ¬(24=10 ∧ c.val=10) →
    0 < min (baseRat (1/(24:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(24:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(24:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(24:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(24:ℚ))*logLoRat 24+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_25 : ∀ c : Fin 31, 2 ≤ c.val →
    ¬(25=10 ∧ c.val=10) →
    0 < min (baseRat (1/(25:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(25:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(25:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(25:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(25:ℚ))*logLoRat 25+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_26 : ∀ c : Fin 31, 2 ≤ c.val →
    ¬(26=10 ∧ c.val=10) →
    0 < min (baseRat (1/(26:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(26:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(26:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(26:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(26:ℚ))*logLoRat 26+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_27 : ∀ c : Fin 31, 2 ≤ c.val →
    ¬(27=10 ∧ c.val=10) →
    0 < min (baseRat (1/(27:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(27:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(27:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(27:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(27:ℚ))*logLoRat 27+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_28 : ∀ c : Fin 31, 2 ≤ c.val →
    ¬(28=10 ∧ c.val=10) →
    0 < min (baseRat (1/(28:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(28:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(28:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(28:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(28:ℚ))*logLoRat 28+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_29 : ∀ c : Fin 31, 2 ≤ c.val →
    ¬(29=10 ∧ c.val=10) →
    0 < min (baseRat (1/(29:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(29:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(29:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(29:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(29:ℚ))*logLoRat 29+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate_row_30 : ∀ c : Fin 31, 2 ≤ c.val →
    ¬(30=10 ∧ c.val=10) →
    0 < min (baseRat (1/(30:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(30:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(30:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(30:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(30:ℚ))*logLoRat 30+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_gate : ∀ d c : Fin 31, 2 ≤ d.val → 2 ≤ c.val →
    ¬(d.val=10 ∧ c.val=10) →
    0 < min (baseRat (1/(d.val:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(d.val:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(d.val:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(d.val:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(d.val:ℚ))*logLoRat d.val+(1/(c.val:ℚ))*logLoRat c.val := by
  intro d c hd hc hn
  have hdN : d.val ≤ 30 := by omega
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
  · simpa only [Nat.cast_ofNat] using finite_gate_row_28 c hc hn
  · simpa only [Nat.cast_ofNat] using finite_gate_row_29 c hc hn
  · simpa only [Nat.cast_ofNat] using finite_gate_row_30 c hc hn

theorem finite_strict_nat (d c : ℕ) (hd0 : 2 ≤ d) (hc0 : 2 ≤ c)
    (hdN : d ≤ 30) (hcN : c ≤ 30) (hn : ¬(d=10 ∧ c=10)) :
    0 < edgeCost 10 quadraticAnchor d c := by
  have hdp : 0 < d := by omega
  have hcp : 0 < c := by omega
  have hg := finite_gate ⟨d,by omega⟩ ⟨c,by omega⟩ hd0 hc0 hn
  have h := rational_edge_gate (baseRat (1/(d:ℚ)) (1/(c:ℚ)))
    (slopeRat (1/(d:ℚ)) (1/(c:ℚ))) gammaLoRat gammaHiRat
    (1/(d:ℚ)) (1/(c:ℚ)) (logLoRat d) (logLoRat c)
    (gamma 10) (log (10/(d:ℝ))) (log (10/(c:ℝ)))
    (by positivity) (by positivity) gamma_rat_bounds.1 gamma_rat_bounds.2
    (degree_log_lower d hd0 hdN) (degree_log_lower c hc0 hcN) hg
  have hm := model_rational (1/(d:ℚ)) (1/(c:ℚ))
  push_cast at h hm
  rw [edge_value_model d c (by positivity) (by positivity), hm]
  exact h

theorem finite_strict (d c : ℤ) (hd0 : 2 ≤ d) (hc0 : 2 ≤ c)
    (hdN : d ≤ 30) (hcN : c ≤ 30) (hn : ¬(d=10 ∧ c=10)) :
    0 < edgeCost 10 quadraticAnchor d c := by
  have hd : (d.toNat:ℤ) = d := Int.toNat_of_nonneg (by omega)
  have hc : (c.toNat:ℤ) = c := Int.toNat_of_nonneg (by omega)
  have h := finite_strict_nat d.toNat c.toNat (by omega) (by omega) (by omega) (by omega)
    (by intro hh; apply hn; constructor <;> omega)
  rw [← hd, ← hc]
  simpa only [Int.cast_natCast] using h

end SparseComponent.TotalFamily.Density10
