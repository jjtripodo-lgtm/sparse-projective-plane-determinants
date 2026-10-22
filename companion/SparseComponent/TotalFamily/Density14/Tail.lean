import SparseComponent.TotalFamily.Density14.Finite
import SparseComponent.TotalFamily.PolynomialEnvelope

namespace SparseComponent.TotalFamily.Density14
open Finset Matrix Real TotalOnes
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem tail_log (y : ℝ) (hy : 0 < y) (hY : y ≤ 1/43) :
    ((-112214279:ℝ)/4300000000) ≤ y*log (14*y) := by
  have hl : log ((14:ℝ)*(1/43)) ≤ -1 := by
    rw [show (14:ℝ)*(1/43) = (((43:ℝ)/14))⁻¹ by norm_num, log_inv]
    linarith [log_43_14.1]
  have h := xlog_tail_lower 14 (1/43) y (by norm_num) (by norm_num) hy hY hl
  have hb := mul_le_mul_of_nonneg_left ratio_log_lower_43 (by norm_num : (0:ℝ) ≤ 1/43)
  norm_num at h hb ⊢
  linarith

def tailU : ℚ := ((1:ℚ)/43)
def tailLoRat : ℚ := ((-112214279:ℚ)/4300000000)

def aCoeff (x : ℚ) (j : Fin 8) : ℚ :=
  match j.val with
  | 0 => ((1:ℚ)/13)*x^1 + ((6:ℚ)/91)*x^0
  | 1 => ((-196:ℚ)/13)*x^1 + ((1:ℚ)/13)*x^0
  | 2 => ((0:ℚ)/1)*x^0
  | 3 => ((0:ℚ)/1)*x^0
  | 4 => ((0:ℚ)/1)*x^0
  | 5 => ((0:ℚ)/1)*x^0
  | 6 => ((0:ℚ)/1)*x^0
  | 7 => ((0:ℚ)/1)*x^0
  | _ => 0

def bCoeff (x : ℚ) (j : Fin 8) : ℚ :=
  match j.val with
  | 0 => ((-86436:ℚ)/1)*x^7 + ((-39788:ℚ)/1)*x^6 + ((1070993:ℚ)/9)*x^5 + ((253022:ℚ)/9)*x^4 + ((-176983:ℚ)/4)*x^3 + ((59267:ℚ)/252)*x^2 + ((-1385185:ℚ)/7056)*x^1 + ((27:ℚ)/1)*x^0
  | 1 => ((-115248:ℚ)/1)*x^4 + ((-137200:ℚ)/3)*x^3 + ((247156:ℚ)/3)*x^2 + ((-16604:ℚ)/3)*x^1 + ((-1385185:ℚ)/7056)*x^0
  | 2 => ((247156:ℚ)/3)*x^1 + ((59267:ℚ)/252)*x^0
  | 3 => ((-137200:ℚ)/3)*x^1 + ((-176983:ℚ)/4)*x^0
  | 4 => ((-115248:ℚ)/1)*x^1 + ((253022:ℚ)/9)*x^0
  | 5 => ((1070993:ℚ)/9)*x^0
  | 6 => ((-39788:ℚ)/1)*x^0
  | 7 => ((-86436:ℚ)/1)*x^0
  | _ => 0

def monoA (k : Fin 22) : ℚ :=
  match k.val with
  | 0 => ((0:ℚ)/1)
  | 1 => ((0:ℚ)/1)
  | 2 => ((0:ℚ)/1)
  | 3 => ((0:ℚ)/1)
  | 4 => ((0:ℚ)/1)
  | 5 => ((0:ℚ)/1)
  | 6 => ((0:ℚ)/1)
  | 7 => ((0:ℚ)/1)
  | 8 => ((0:ℚ)/1)
  | 9 => ((0:ℚ)/1)
  | 10 => ((0:ℚ)/1)
  | 11 => ((0:ℚ)/1)
  | 12 => ((-196:ℚ)/13)
  | 13 => ((1:ℚ)/13)
  | 14 => ((0:ℚ)/1)
  | 15 => ((0:ℚ)/1)
  | 16 => ((0:ℚ)/1)
  | 17 => ((0:ℚ)/1)
  | 18 => ((0:ℚ)/1)
  | 19 => ((0:ℚ)/1)
  | 20 => ((1:ℚ)/13)
  | 21 => ((6:ℚ)/91)
  | _ => 0

def monoB (k : Fin 22) : ℚ :=
  match k.val with
  | 0 => ((-86436:ℚ)/1)
  | 1 => ((-39788:ℚ)/1)
  | 2 => ((1070993:ℚ)/9)
  | 3 => ((-115248:ℚ)/1)
  | 4 => ((253022:ℚ)/9)
  | 5 => ((-137200:ℚ)/3)
  | 6 => ((-176983:ℚ)/4)
  | 7 => ((247156:ℚ)/3)
  | 8 => ((59267:ℚ)/252)
  | 9 => ((-115248:ℚ)/1)
  | 10 => ((-137200:ℚ)/3)
  | 11 => ((247156:ℚ)/3)
  | 12 => ((-16604:ℚ)/3)
  | 13 => ((-1385185:ℚ)/7056)
  | 14 => ((-86436:ℚ)/1)
  | 15 => ((-39788:ℚ)/1)
  | 16 => ((1070993:ℚ)/9)
  | 17 => ((253022:ℚ)/9)
  | 18 => ((-176983:ℚ)/4)
  | 19 => ((59267:ℚ)/252)
  | 20 => ((-1385185:ℚ)/7056)
  | 21 => ((27:ℚ)/1)
  | _ => 0

def monoIX (k : Fin 22) : ℕ :=
  match k.val with
  | 0 => 7
  | 1 => 6
  | 2 => 5
  | 3 => 4
  | 4 => 4
  | 5 => 3
  | 6 => 3
  | 7 => 2
  | 8 => 2
  | 9 => 1
  | 10 => 1
  | 11 => 1
  | 12 => 1
  | 13 => 1
  | 14 => 0
  | 15 => 0
  | 16 => 0
  | 17 => 0
  | 18 => 0
  | 19 => 0
  | 20 => 0
  | 21 => 0
  | _ => 0

def monoIY (k : Fin 22) : ℕ :=
  match k.val with
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 1
  | 4 => 0
  | 5 => 1
  | 6 => 0
  | 7 => 1
  | 8 => 0
  | 9 => 4
  | 10 => 3
  | 11 => 2
  | 12 => 1
  | 13 => 0
  | 14 => 7
  | 15 => 6
  | 16 => 5
  | 17 => 4
  | 18 => 3
  | 19 => 2
  | 20 => 1
  | 21 => 0
  | _ => 0

theorem mixed_model (X : ℚ) (y : ℝ) :
    poly (X:ℝ) y = boxPolynomial (aCoeff X) (bCoeff X) (fun _ => 0) (fun j => j.val) (gamma 14) 0 y := by
  unfold poly boxPolynomial
  generalize gamma 14 = g
  norm_num [aCoeff,bCoeff,Fin.sum_univ_succ]
  push_cast
  ring

theorem double_model (x y : ℝ) :
    poly x y = boxPolynomial monoA monoB monoIX monoIY (gamma 14) x y := by
  unfold poly boxPolynomial
  generalize gamma 14 = g
  norm_num [monoA,monoB,monoIX,monoIY,Fin.sum_univ_succ]
  ring

theorem tail_log_rat (y : ℝ) (hy : 0 < y) (hY : y ≤ (tailU:ℝ)) :
    (tailLoRat:ℝ) ≤ y*log (14*y) := by
  have hU : y ≤ 1/43 := by convert hY using 1 <;> norm_num [tailU]
  have h := tail_log y hy hU
  convert h using 1 <;> norm_num [tailLoRat]

theorem mixed_gate : ∀ d : Fin 43, 3 ≤ d.val →
    0 < boxEnvelope (aCoeff (1/(d.val:ℚ))) (bCoeff (1/(d.val:ℚ)))
        (fun _ => 0) (fun j => j.val) gammaLoRat gammaHiRat tailU +
      (1/(d.val:ℚ))*logLoRat d.val+tailLoRat := by
  decide +kernel

theorem double_gate :
    0 < boxEnvelope monoA monoB monoIX monoIY gammaLoRat gammaHiRat tailU+2*tailLoRat := by
  decide +kernel

theorem mixed_compact (d : ℕ) (hd : 3 ≤ d) (hD : d ≤ 42)
    (y : ℝ) (hy : 0 < y) (hY : y ≤ (tailU:ℝ)) :
    0 < poly (1/(d:ℝ)) y+(1/(d:ℝ))*log (14/(d:ℝ))+y*log (14*y) := by
  have hp := boxEnvelope_lower (aCoeff (1/(d:ℚ))) (bCoeff (1/(d:ℚ)))
    (fun _ => 0) (fun j => j.val) gammaLoRat gammaHiRat tailU (gamma 14) 0 y
    gamma_rat_bounds.1 gamma_rat_bounds.2 (by norm_num) hy.le (by norm_num [tailU]) hY
  rw [← mixed_model] at hp
  push_cast at hp
  have hx := mul_le_mul_of_nonneg_left (degree_log_lower d hd hD) (by positivity : (0:ℝ) ≤ 1/(d:ℝ))
  have ht := tail_log_rat y hy hY
  have hg := mixed_gate ⟨d,by omega⟩ hd
  dsimp only at hg
  have hb : (0:ℝ) < (boxEnvelope (aCoeff (1/(d:ℚ))) (bCoeff (1/(d:ℚ)))
      (fun _ => 0) (fun j => j.val) gammaLoRat gammaHiRat tailU:ℝ)+
      (1/(d:ℝ))*(logLoRat d:ℝ)+(tailLoRat:ℝ) := by
    have hz := Rat.cast_pos_of_pos (K := ℝ) hg
    simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_one, Rat.cast_natCast] using hz
  linarith only [hp,hx,ht,hb]

theorem double_compact (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hX : x ≤ (tailU:ℝ)) (hY : y ≤ (tailU:ℝ)) :
    0 < poly x y+x*log (14*x)+y*log (14*y) := by
  have hp := boxEnvelope_lower monoA monoB monoIX monoIY gammaLoRat gammaHiRat tailU
    (gamma 14) x y gamma_rat_bounds.1 gamma_rat_bounds.2 hx.le hy.le hX hY
  rw [← double_model] at hp
  have hxlog := tail_log_rat x hx hX
  have hylog := tail_log_rat y hy hY
  have hb : (0:ℝ) < (boxEnvelope monoA monoB monoIX monoIY gammaLoRat gammaHiRat tailU:ℝ)+
      2*(tailLoRat:ℝ) := by exact_mod_cast double_gate
  linarith only [hp,hxlog,hylog,hb]

theorem strict_of_nonplane (d c : ℤ) (hd : 2 < d) (hc : 2 < c) (hn : ¬(d=14 ∧ c=14)) :
    0 < edgeCost 14 (cubicAnchor 14) d c := by
  have hd0 : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hc0 : (0:ℝ) < c := by exact_mod_cast (show 0 < c by omega)
  have recip_tail (z : ℤ) (hz : 42 < z) : 1/(z:ℝ) ≤ (tailU:ℝ) := by
    have h : 1/(z:ℝ) ≤ 1/43 := one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast (show 43 ≤ z by omega))
    convert h using 1 <;> norm_num [tailU]
  by_cases hdN : d ≤ 42
  · by_cases hcN : c ≤ 42
    · exact finite_strict d c (by omega) (by omega) hdN hcN hn
    · rw [edge_value d c hd0.ne' hc0.ne']
      have hm := mixed_compact d.toNat (by omega) (by omega) (1/(c:ℝ)) (one_div_pos.mpr hc0) (recip_tail c (by omega))
      have hdc : (d.toNat:ℝ) = d := by exact_mod_cast (Int.toNat_of_nonneg (show 0 ≤ d by omega))
      rw [hdc] at hm
      simpa only [div_eq_mul_inv,one_mul] using hm
  · by_cases hcN : c ≤ 42
    · rw [edgeCost_symm, edge_value c d hc0.ne' hd0.ne']
      have hm := mixed_compact c.toNat (by omega) (by omega) (1/(d:ℝ)) (one_div_pos.mpr hd0) (recip_tail d (by omega))
      have hcc : (c.toNat:ℝ) = c := by exact_mod_cast (Int.toNat_of_nonneg (show 0 ≤ c by omega))
      rw [hcc] at hm
      simpa only [div_eq_mul_inv,one_mul] using hm
    · rw [edge_value d c hd0.ne' hc0.ne']
      simpa only [div_eq_mul_inv,one_mul] using double_compact (1/(d:ℝ)) (1/(c:ℝ))
        (one_div_pos.mpr hd0) (one_div_pos.mpr hc0) (recip_tail d (by omega)) (recip_tail c (by omega))

end SparseComponent.TotalFamily.Density14
