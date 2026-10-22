import SparseComponent.TotalFamily.Density11.Finite
import SparseComponent.TotalFamily.PolynomialEnvelope

namespace SparseComponent.TotalFamily.Density11
open Finset Matrix Real TotalOnes
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem tail_log (y : ℝ) (hy : 0 < y) (hY : y ≤ 1/34) :
    ((-56423263:ℝ)/1700000000) ≤ y*log (11*y) := by
  have hl : log ((11:ℝ)*(1/34)) ≤ -1 := by
    rw [show (11:ℝ)*(1/34) = (((34:ℝ)/11))⁻¹ by norm_num, log_inv]
    linarith [log_34_11.1]
  have h := xlog_tail_lower 11 (1/34) y (by norm_num) (by norm_num) hy hY hl
  have hb := mul_le_mul_of_nonneg_left ratio_log_lower_34 (by norm_num : (0:ℝ) ≤ 1/34)
  norm_num at h hb ⊢
  linarith

def tailU : ℚ := ((1:ℚ)/34)
def tailLoRat : ℚ := ((-56423263:ℚ)/1700000000)

def aCoeff (x : ℚ) (j : Fin 4) : ℚ :=
  match j.val with
  | 0 => ((1:ℚ)/10)*x^1 + ((9:ℚ)/110)*x^0
  | 1 => ((-121:ℚ)/10)*x^1 + ((1:ℚ)/10)*x^0
  | 2 => ((0:ℚ)/1)*x^0
  | 3 => ((0:ℚ)/1)*x^0
  | _ => 0

def bCoeff (x : ℚ) (j : Fin 4) : ℚ :=
  match j.val with
  | 0 => ((-131769:ℚ)/25)*x^3 + ((-15972:ℚ)/25)*x^2 + ((-3509:ℚ)/25)*x^1 + ((21:ℚ)/1)*x^0
  | 1 => ((-14641:ℚ)/2)*x^3 + ((87846:ℚ)/5)*x^2 + ((-1452:ℚ)/5)*x^1 + ((-3509:ℚ)/25)*x^0
  | 2 => ((87846:ℚ)/5)*x^1 + ((-15972:ℚ)/25)*x^0
  | 3 => ((-14641:ℚ)/2)*x^1 + ((-131769:ℚ)/25)*x^0
  | _ => 0

def monoA (k : Fin 12) : ℚ :=
  match k.val with
  | 0 => ((0:ℚ)/1)
  | 1 => ((0:ℚ)/1)
  | 2 => ((0:ℚ)/1)
  | 3 => ((0:ℚ)/1)
  | 4 => ((0:ℚ)/1)
  | 5 => ((0:ℚ)/1)
  | 6 => ((-121:ℚ)/10)
  | 7 => ((1:ℚ)/10)
  | 8 => ((0:ℚ)/1)
  | 9 => ((0:ℚ)/1)
  | 10 => ((1:ℚ)/10)
  | 11 => ((9:ℚ)/110)
  | _ => 0

def monoB (k : Fin 12) : ℚ :=
  match k.val with
  | 0 => ((-14641:ℚ)/2)
  | 1 => ((-131769:ℚ)/25)
  | 2 => ((87846:ℚ)/5)
  | 3 => ((-15972:ℚ)/25)
  | 4 => ((-14641:ℚ)/2)
  | 5 => ((87846:ℚ)/5)
  | 6 => ((-1452:ℚ)/5)
  | 7 => ((-3509:ℚ)/25)
  | 8 => ((-131769:ℚ)/25)
  | 9 => ((-15972:ℚ)/25)
  | 10 => ((-3509:ℚ)/25)
  | 11 => ((21:ℚ)/1)
  | _ => 0

def monoIX (k : Fin 12) : ℕ :=
  match k.val with
  | 0 => 3
  | 1 => 3
  | 2 => 2
  | 3 => 2
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | 7 => 1
  | 8 => 0
  | 9 => 0
  | 10 => 0
  | 11 => 0
  | _ => 0

def monoIY (k : Fin 12) : ℕ :=
  match k.val with
  | 0 => 1
  | 1 => 0
  | 2 => 1
  | 3 => 0
  | 4 => 3
  | 5 => 2
  | 6 => 1
  | 7 => 0
  | 8 => 3
  | 9 => 2
  | 10 => 1
  | 11 => 0
  | _ => 0

theorem mixed_model (X : ℚ) (y : ℝ) :
    poly (X:ℝ) y = boxPolynomial (aCoeff X) (bCoeff X) (fun _ => 0) (fun j => j.val) (gamma 11) 0 y := by
  unfold poly boxPolynomial
  generalize gamma 11 = g
  norm_num [aCoeff,bCoeff,Fin.sum_univ_succ]
  push_cast
  ring

theorem double_model (x y : ℝ) :
    poly x y = boxPolynomial monoA monoB monoIX monoIY (gamma 11) x y := by
  unfold poly boxPolynomial
  generalize gamma 11 = g
  norm_num [monoA,monoB,monoIX,monoIY,Fin.sum_univ_succ]
  ring

theorem tail_log_rat (y : ℝ) (hy : 0 < y) (hY : y ≤ (tailU:ℝ)) :
    (tailLoRat:ℝ) ≤ y*log (11*y) := by
  have hU : y ≤ 1/34 := by convert hY using 1 <;> norm_num [tailU]
  have h := tail_log y hy hU
  convert h using 1 <;> norm_num [tailLoRat]

theorem mixed_gate : ∀ d : Fin 34, 3 ≤ d.val →
    0 < boxEnvelope (aCoeff (1/(d.val:ℚ))) (bCoeff (1/(d.val:ℚ)))
        (fun _ => 0) (fun j => j.val) gammaLoRat gammaHiRat tailU +
      (1/(d.val:ℚ))*logLoRat d.val+tailLoRat := by
  decide +kernel

theorem double_gate :
    0 < boxEnvelope monoA monoB monoIX monoIY gammaLoRat gammaHiRat tailU+2*tailLoRat := by
  decide +kernel

theorem mixed_compact (d : ℕ) (hd : 3 ≤ d) (hD : d ≤ 33)
    (y : ℝ) (hy : 0 < y) (hY : y ≤ (tailU:ℝ)) :
    0 < poly (1/(d:ℝ)) y+(1/(d:ℝ))*log (11/(d:ℝ))+y*log (11*y) := by
  have hp := boxEnvelope_lower (aCoeff (1/(d:ℚ))) (bCoeff (1/(d:ℚ)))
    (fun _ => 0) (fun j => j.val) gammaLoRat gammaHiRat tailU (gamma 11) 0 y
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
    0 < poly x y+x*log (11*x)+y*log (11*y) := by
  have hp := boxEnvelope_lower monoA monoB monoIX monoIY gammaLoRat gammaHiRat tailU
    (gamma 11) x y gamma_rat_bounds.1 gamma_rat_bounds.2 hx.le hy.le hX hY
  rw [← double_model] at hp
  have hxlog := tail_log_rat x hx hX
  have hylog := tail_log_rat y hy hY
  have hb : (0:ℝ) < (boxEnvelope monoA monoB monoIX monoIY gammaLoRat gammaHiRat tailU:ℝ)+
      2*(tailLoRat:ℝ) := by exact_mod_cast double_gate
  linarith only [hp,hxlog,hylog,hb]

theorem strict_of_nonplane (d c : ℤ) (hd : 2 < d) (hc : 2 < c) (hn : ¬(d=11 ∧ c=11)) :
    0 < edgeCost 11 (linearAnchor 11) d c := by
  have hd0 : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hc0 : (0:ℝ) < c := by exact_mod_cast (show 0 < c by omega)
  have recip_tail (z : ℤ) (hz : 33 < z) : 1/(z:ℝ) ≤ (tailU:ℝ) := by
    have h : 1/(z:ℝ) ≤ 1/34 := one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast (show 34 ≤ z by omega))
    convert h using 1 <;> norm_num [tailU]
  by_cases hdN : d ≤ 33
  · by_cases hcN : c ≤ 33
    · exact finite_strict d c (by omega) (by omega) hdN hcN hn
    · rw [edge_value d c hd0.ne' hc0.ne']
      have hm := mixed_compact d.toNat (by omega) (by omega) (1/(c:ℝ)) (one_div_pos.mpr hc0) (recip_tail c (by omega))
      have hdc : (d.toNat:ℝ) = d := by exact_mod_cast (Int.toNat_of_nonneg (show 0 ≤ d by omega))
      rw [hdc] at hm
      simpa only [div_eq_mul_inv,one_mul] using hm
  · by_cases hcN : c ≤ 33
    · rw [edgeCost_symm, edge_value c d hc0.ne' hd0.ne']
      have hm := mixed_compact c.toNat (by omega) (by omega) (1/(d:ℝ)) (one_div_pos.mpr hd0) (recip_tail d (by omega))
      have hcc : (c.toNat:ℝ) = c := by exact_mod_cast (Int.toNat_of_nonneg (show 0 ≤ c by omega))
      rw [hcc] at hm
      simpa only [div_eq_mul_inv,one_mul] using hm
    · rw [edge_value d c hd0.ne' hc0.ne']
      simpa only [div_eq_mul_inv,one_mul] using double_compact (1/(d:ℝ)) (1/(c:ℝ))
        (one_div_pos.mpr hd0) (one_div_pos.mpr hc0) (recip_tail d (by omega)) (recip_tail c (by omega))

end SparseComponent.TotalFamily.Density11
