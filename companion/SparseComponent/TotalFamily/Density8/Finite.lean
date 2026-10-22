import SparseComponent.TotalFamily.Density8.LogBounds
import SparseComponent.TotalFamily.FiniteCertificateTools

namespace SparseComponent.TotalFamily.Density8
open Finset Matrix Real TotalOnes
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

noncomputable def poly (x y : ℝ) : ℝ :=
  (((0:ℝ)/1)+((-2048:ℝ)/1)*gamma 8)*x^3*y^1 +
  (((0:ℝ)/1)+((-36864:ℝ)/25)*gamma 8)*x^3*y^0 +
  (((0:ℝ)/1)+((24576:ℝ)/5)*gamma 8)*x^2*y^1 +
  (((0:ℝ)/1)+((-6144:ℝ)/25)*gamma 8)*x^2*y^0 +
  (((0:ℝ)/1)+((-2048:ℝ)/1)*gamma 8)*x^1*y^3 +
  (((0:ℝ)/1)+((24576:ℝ)/5)*gamma 8)*x^1*y^2 +
  (((-64:ℝ)/7)+((-384:ℝ)/5)*gamma 8)*x^1*y^1 +
  (((1:ℝ)/7)+((-1856:ℝ)/25)*gamma 8)*x^1*y^0 +
  (((0:ℝ)/1)+((-36864:ℝ)/25)*gamma 8)*x^0*y^3 +
  (((0:ℝ)/1)+((-6144:ℝ)/25)*gamma 8)*x^0*y^2 +
  (((1:ℝ)/7)+((-1856:ℝ)/25)*gamma 8)*x^0*y^1 +
  (((3:ℝ)/28)+((15:ℝ)/1)*gamma 8)*x^0*y^0

theorem poly_identity (x y : ℝ) : polynomialModel 8 (linearAnchor 8) x y = poly x y := by
  unfold polynomialModel linearAnchor poly
  generalize gamma 8 = g
  norm_num
  ring

theorem edge_value (d c : ℝ) (hd : d ≠ 0) (hc : c ≠ 0) :
    edgeCost 8 (linearAnchor 8) d c = poly (1/d) (1/c)+(1/d)*log (8/d)+(1/c)*log (8/c) := by
  have h := edgeCost_reciprocal 8 (1/d) (1/c) (by norm_num) (one_div_ne_zero hd) (one_div_ne_zero hc) (linearAnchor 8)
  simp only [one_div_one_div] at h
  rw [h, polynomial_edge_identity 8 (1/d) (1/c) (by norm_num), poly_identity]
  simp only [div_eq_mul_inv, one_mul]

theorem edge_value_model (d c : ℝ) (hd : d ≠ 0) (hc : c ≠ 0) :
    edgeCost 8 (linearAnchor 8) d c = polynomialModel 8 (linearAnchor 8) (1/d) (1/c)+(1/d)*log (8/d)+(1/c)*log (8/c) := by
  rw [edge_value d c hd hc, poly_identity]

def anchorRat (z : ℚ) : ℚ := 2/(5*8)+(3/5)*z
def baseRat (x y : ℚ) : ℚ := 2/8-1/(8-1)+(x+y)/(8-1)-8^2/(8-1)*x*y
def slopeRat (x y : ℚ) : ℚ :=
  2*8-1-8^2*(x+y)-2*8^2*(8-1)*x*y +
  8^4*(-x*(anchorRat x)^2-y*(anchorRat y)^2+
    2*x*y*(anchorRat x+anchorRat y)-(x^3*y+x*y^3)/2)
def gammaLoRat : ℚ := ((182514133:ℚ)/100000000000)
def gammaHiRat : ℚ := ((91257067:ℚ)/50000000000)
def logLoRat : ℕ → ℚ
  | 2 => ((34657359:ℚ)/25000000)
  | 3 => ((3923317:ℚ)/4000000)
  | 4 => ((34657359:ℚ)/50000000)
  | 5 => ((23500181:ℚ)/50000000)
  | 6 => ((28768207:ℚ)/100000000)
  | 7 => ((13353139:ℚ)/100000000)
  | 8 => ((0:ℚ)/1)
  | 9 => ((-46009:ℚ)/390625)
  | 10 => ((-5578589:ℚ)/25000000)
  | 11 => ((-15922687:ℚ)/50000000)
  | 12 => ((-40546511:ℚ)/100000000)
  | 13 => ((-24275391:ℚ)/50000000)
  | 14 => ((-55961579:ℚ)/100000000)
  | 15 => ((-31430433:ℚ)/50000000)
  | 16 => ((-69314719:ℚ)/100000000)
  | 17 => ((-75377181:ℚ)/100000000)
  | 18 => ((-40546511:ℚ)/50000000)
  | 19 => ((-2703117:ℚ)/3125000)
  | 20 => ((-45814537:ℚ)/50000000)
  | 21 => ((-9650809:ℚ)/10000000)
  | 22 => ((-25290023:ℚ)/25000000)
  | 23 => ((-26401317:ℚ)/25000000)
  | 24 => ((-109861229:ℚ)/100000000)
  | _ => 0

theorem model_rational (x y : ℚ) :
    polynomialModel 8 (linearAnchor 8) (x:ℝ) (y:ℝ) = (baseRat x y:ℝ)+(slopeRat x y:ℝ)*gamma 8 := by
  unfold polynomialModel linearAnchor baseRat slopeRat anchorRat
  generalize gamma 8 = g
  push_cast
  norm_num
  ring

theorem gamma_rat_bounds : (gammaLoRat:ℝ) ≤ gamma 8 ∧ gamma 8 ≤ (gammaHiRat:ℝ) := by
  norm_num only [gammaLoRat, gammaHiRat, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg]
  exact gamma_bounds

theorem degree_log_lower (d : ℕ) (hd : 2 ≤ d) (hD : d ≤ 24) :
    (logLoRat d:ℝ) ≤ log (8/(d:ℝ)) := by
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

/-- The finite rational table is checked by kernel reduction; no native evaluator is trusted. -/
theorem finite_gate : ∀ d c : Fin 25, 2 ≤ d.val → 2 ≤ c.val →
    ¬(d.val=8 ∧ c.val=8) →
    0 < min (baseRat (1/(d.val:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(d.val:ℚ)) (1/(c.val:ℚ))*gammaLoRat)
        (baseRat (1/(d.val:ℚ)) (1/(c.val:ℚ))+
          slopeRat (1/(d.val:ℚ)) (1/(c.val:ℚ))*gammaHiRat) +
      (1/(d.val:ℚ))*logLoRat d.val+(1/(c.val:ℚ))*logLoRat c.val := by
  decide +kernel

theorem finite_strict_nat (d c : ℕ) (hd0 : 2 ≤ d) (hc0 : 2 ≤ c)
    (hdN : d ≤ 24) (hcN : c ≤ 24) (hn : ¬(d=8 ∧ c=8)) :
    0 < edgeCost 8 (linearAnchor 8) d c := by
  have hdp : 0 < d := by omega
  have hcp : 0 < c := by omega
  have hg := finite_gate ⟨d,by omega⟩ ⟨c,by omega⟩ hd0 hc0 hn
  have h := rational_edge_gate (baseRat (1/(d:ℚ)) (1/(c:ℚ)))
    (slopeRat (1/(d:ℚ)) (1/(c:ℚ))) gammaLoRat gammaHiRat
    (1/(d:ℚ)) (1/(c:ℚ)) (logLoRat d) (logLoRat c)
    (gamma 8) (log (8/(d:ℝ))) (log (8/(c:ℝ)))
    (by positivity) (by positivity) gamma_rat_bounds.1 gamma_rat_bounds.2
    (degree_log_lower d hd0 hdN) (degree_log_lower c hc0 hcN) hg
  have hm := model_rational (1/(d:ℚ)) (1/(c:ℚ))
  push_cast at h hm
  rw [edge_value_model d c (by positivity) (by positivity), hm]
  exact h

theorem finite_strict (d c : ℤ) (hd0 : 2 ≤ d) (hc0 : 2 ≤ c)
    (hdN : d ≤ 24) (hcN : c ≤ 24) (hn : ¬(d=8 ∧ c=8)) :
    0 < edgeCost 8 (linearAnchor 8) d c := by
  have hd : (d.toNat:ℤ) = d := Int.toNat_of_nonneg (by omega)
  have hc : (c.toNat:ℤ) = c := Int.toNat_of_nonneg (by omega)
  have h := finite_strict_nat d.toNat c.toNat (by omega) (by omega) (by omega) (by omega)
    (by intro hh; apply hn; constructor <;> omega)
  rw [← hd, ← hc]
  simpa only [Int.cast_natCast] using h

end SparseComponent.TotalFamily.Density8
