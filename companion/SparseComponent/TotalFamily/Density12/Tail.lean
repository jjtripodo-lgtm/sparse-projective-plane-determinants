import SparseComponent.TotalFamily.Density12.Finite
import SparseComponent.TotalFamily.PolynomialEnvelope

namespace SparseComponent.TotalFamily.Density12
open Finset Matrix Real TotalOnes
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem tail_log (y : ℝ) (hy : 0 < y) (hY : y ≤ 1/37) :
    ((-112601127:ℝ)/3700000000) ≤ y*log (12*y) := by
  have hl : log ((12:ℝ)*(1/37)) ≤ -1 := by
    rw [show (12:ℝ)*(1/37) = (((37:ℝ)/12))⁻¹ by norm_num, log_inv]
    linarith [log_37_12.1]
  have h := xlog_tail_lower 12 (1/37) y (by norm_num) (by norm_num) hy hY hl
  have hb := mul_le_mul_of_nonneg_left ratio_log_lower_37 (by norm_num : (0:ℝ) ≤ 1/37)
  norm_num at h hb ⊢
  linarith

def tailU : ℚ := ((1:ℚ)/37)
def tailLoRat : ℚ := ((-112601127:ℚ)/3700000000)

def aCoeff (x : ℚ) (j : Fin 8) : ℚ :=
  match j.val with
  | 0 => ((1:ℚ)/11)*x^1 + ((5:ℚ)/66)*x^0
  | 1 => ((-144:ℚ)/11)*x^1 + ((1:ℚ)/11)*x^0
  | 2 => ((0:ℚ)/1)*x^0
  | 3 => ((0:ℚ)/1)*x^0
  | 4 => ((0:ℚ)/1)*x^0
  | 5 => ((0:ℚ)/1)*x^0
  | 6 => ((0:ℚ)/1)*x^0
  | 7 => ((0:ℚ)/1)*x^0
  | _ => 0

def bCoeff (x : ℚ) (j : Fin 8) : ℚ :=
  match j.val with
  | 0 => ((-46656:ℚ)/1)*x^7 + ((-18144:ℚ)/1)*x^6 + ((65412:ℚ)/1)*x^5 + ((12828:ℚ)/1)*x^4 + ((-96903:ℚ)/4)*x^3 + ((4043:ℚ)/24)*x^2 + ((-83113:ℚ)/576)*x^1 + ((23:ℚ)/1)*x^0
  | 1 => ((-62208:ℚ)/1)*x^4 + ((-22464:ℚ)/1)*x^3 + ((44784:ℚ)/1)*x^2 + ((-3480:ℚ)/1)*x^1 + ((-83113:ℚ)/576)*x^0
  | 2 => ((44784:ℚ)/1)*x^1 + ((4043:ℚ)/24)*x^0
  | 3 => ((-22464:ℚ)/1)*x^1 + ((-96903:ℚ)/4)*x^0
  | 4 => ((-62208:ℚ)/1)*x^1 + ((12828:ℚ)/1)*x^0
  | 5 => ((65412:ℚ)/1)*x^0
  | 6 => ((-18144:ℚ)/1)*x^0
  | 7 => ((-46656:ℚ)/1)*x^0
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
  | 12 => ((-144:ℚ)/11)
  | 13 => ((1:ℚ)/11)
  | 14 => ((0:ℚ)/1)
  | 15 => ((0:ℚ)/1)
  | 16 => ((0:ℚ)/1)
  | 17 => ((0:ℚ)/1)
  | 18 => ((0:ℚ)/1)
  | 19 => ((0:ℚ)/1)
  | 20 => ((1:ℚ)/11)
  | 21 => ((5:ℚ)/66)
  | _ => 0

def monoB (k : Fin 22) : ℚ :=
  match k.val with
  | 0 => ((-46656:ℚ)/1)
  | 1 => ((-18144:ℚ)/1)
  | 2 => ((65412:ℚ)/1)
  | 3 => ((-62208:ℚ)/1)
  | 4 => ((12828:ℚ)/1)
  | 5 => ((-22464:ℚ)/1)
  | 6 => ((-96903:ℚ)/4)
  | 7 => ((44784:ℚ)/1)
  | 8 => ((4043:ℚ)/24)
  | 9 => ((-62208:ℚ)/1)
  | 10 => ((-22464:ℚ)/1)
  | 11 => ((44784:ℚ)/1)
  | 12 => ((-3480:ℚ)/1)
  | 13 => ((-83113:ℚ)/576)
  | 14 => ((-46656:ℚ)/1)
  | 15 => ((-18144:ℚ)/1)
  | 16 => ((65412:ℚ)/1)
  | 17 => ((12828:ℚ)/1)
  | 18 => ((-96903:ℚ)/4)
  | 19 => ((4043:ℚ)/24)
  | 20 => ((-83113:ℚ)/576)
  | 21 => ((23:ℚ)/1)
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
    poly (X:ℝ) y = boxPolynomial (aCoeff X) (bCoeff X) (fun _ => 0) (fun j => j.val) (gamma 12) 0 y := by
  unfold poly boxPolynomial
  generalize gamma 12 = g
  norm_num [aCoeff,bCoeff,Fin.sum_univ_succ]
  push_cast
  ring

theorem double_model (x y : ℝ) :
    poly x y = boxPolynomial monoA monoB monoIX monoIY (gamma 12) x y := by
  unfold poly boxPolynomial
  generalize gamma 12 = g
  norm_num [monoA,monoB,monoIX,monoIY,Fin.sum_univ_succ]
  ring

theorem tail_log_rat (y : ℝ) (hy : 0 < y) (hY : y ≤ (tailU:ℝ)) :
    (tailLoRat:ℝ) ≤ y*log (12*y) := by
  have hU : y ≤ 1/37 := by convert hY using 1 <;> norm_num [tailU]
  have h := tail_log y hy hU
  convert h using 1 <;> norm_num [tailLoRat]

theorem mixed_gate : ∀ d : Fin 37, 3 ≤ d.val →
    0 < boxEnvelope (aCoeff (1/(d.val:ℚ))) (bCoeff (1/(d.val:ℚ)))
        (fun _ => 0) (fun j => j.val) gammaLoRat gammaHiRat tailU +
      (1/(d.val:ℚ))*logLoRat d.val+tailLoRat := by
  decide +kernel

theorem double_gate :
    0 < boxEnvelope monoA monoB monoIX monoIY gammaLoRat gammaHiRat tailU+2*tailLoRat := by
  decide +kernel

theorem mixed_compact (d : ℕ) (hd : 3 ≤ d) (hD : d ≤ 36)
    (y : ℝ) (hy : 0 < y) (hY : y ≤ (tailU:ℝ)) :
    0 < poly (1/(d:ℝ)) y+(1/(d:ℝ))*log (12/(d:ℝ))+y*log (12*y) := by
  have hp := boxEnvelope_lower (aCoeff (1/(d:ℚ))) (bCoeff (1/(d:ℚ)))
    (fun _ => 0) (fun j => j.val) gammaLoRat gammaHiRat tailU (gamma 12) 0 y
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
    0 < poly x y+x*log (12*x)+y*log (12*y) := by
  have hp := boxEnvelope_lower monoA monoB monoIX monoIY gammaLoRat gammaHiRat tailU
    (gamma 12) x y gamma_rat_bounds.1 gamma_rat_bounds.2 hx.le hy.le hX hY
  rw [← double_model] at hp
  have hxlog := tail_log_rat x hx hX
  have hylog := tail_log_rat y hy hY
  have hb : (0:ℝ) < (boxEnvelope monoA monoB monoIX monoIY gammaLoRat gammaHiRat tailU:ℝ)+
      2*(tailLoRat:ℝ) := by exact_mod_cast double_gate
  linarith only [hp,hxlog,hylog,hb]

theorem strict_of_nonplane (d c : ℤ) (hd : 2 < d) (hc : 2 < c) (hn : ¬(d=12 ∧ c=12)) :
    0 < edgeCost 12 (cubicAnchor 12) d c := by
  have hd0 : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hc0 : (0:ℝ) < c := by exact_mod_cast (show 0 < c by omega)
  have recip_tail (z : ℤ) (hz : 36 < z) : 1/(z:ℝ) ≤ (tailU:ℝ) := by
    have h : 1/(z:ℝ) ≤ 1/37 := one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast (show 37 ≤ z by omega))
    convert h using 1 <;> norm_num [tailU]
  by_cases hdN : d ≤ 36
  · by_cases hcN : c ≤ 36
    · exact finite_strict d c (by omega) (by omega) hdN hcN hn
    · rw [edge_value d c hd0.ne' hc0.ne']
      have hm := mixed_compact d.toNat (by omega) (by omega) (1/(c:ℝ)) (one_div_pos.mpr hc0) (recip_tail c (by omega))
      have hdc : (d.toNat:ℝ) = d := by exact_mod_cast (Int.toNat_of_nonneg (show 0 ≤ d by omega))
      rw [hdc] at hm
      simpa only [div_eq_mul_inv,one_mul] using hm
  · by_cases hcN : c ≤ 36
    · rw [edgeCost_symm, edge_value c d hc0.ne' hd0.ne']
      have hm := mixed_compact c.toNat (by omega) (by omega) (1/(d:ℝ)) (one_div_pos.mpr hd0) (recip_tail d (by omega))
      have hcc : (c.toNat:ℝ) = c := by exact_mod_cast (Int.toNat_of_nonneg (show 0 ≤ c by omega))
      rw [hcc] at hm
      simpa only [div_eq_mul_inv,one_mul] using hm
    · rw [edge_value d c hd0.ne' hc0.ne']
      simpa only [div_eq_mul_inv,one_mul] using double_compact (1/(d:ℝ)) (1/(c:ℝ))
        (one_div_pos.mpr hd0) (one_div_pos.mpr hc0) (recip_tail d (by omega)) (recip_tail c (by omega))

end SparseComponent.TotalFamily.Density12
