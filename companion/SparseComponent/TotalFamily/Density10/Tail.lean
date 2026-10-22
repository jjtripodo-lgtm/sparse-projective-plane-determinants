import SparseComponent.TotalFamily.Density10.Finite
import SparseComponent.TotalFamily.PolynomialEnvelope

namespace SparseComponent.TotalFamily.Density10
open Finset Matrix Real TotalOnes
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem tail_log (y : ℝ) (hy : 0 < y) (hY : y ≤ 1/31) :
    ((-28285053:ℝ)/775000000) ≤ y*log (10*y) := by
  have hl : log ((10:ℝ)*(1/31)) ≤ -1 := by
    rw [show (10:ℝ)*(1/31) = (((31:ℝ)/10))⁻¹ by norm_num, log_inv]
    linarith [log_31_10.1]
  have h := xlog_tail_lower 10 (1/31) y (by norm_num) (by norm_num) hy hY hl
  have hb := mul_le_mul_of_nonneg_left ratio_log_lower_31 (by norm_num : (0:ℝ) ≤ 1/31)
  norm_num at h hb ⊢
  linarith

def tailU : ℚ := ((1:ℚ)/31)
def tailLoRat : ℚ := ((-28285053:ℚ)/775000000)

def aCoeff (x : ℚ) (j : Fin 6) : ℚ :=
  match j.val with
  | 0 => ((1:ℚ)/9)*x^1 + ((4:ℚ)/45)*x^0
  | 1 => ((-100:ℚ)/9)*x^1 + ((1:ℚ)/9)*x^0
  | 2 => ((0:ℚ)/1)*x^0
  | 3 => ((0:ℚ)/1)*x^0
  | 4 => ((0:ℚ)/1)*x^0
  | 5 => ((0:ℚ)/1)*x^0
  | _ => 0

def bCoeff (x : ℚ) (j : Fin 6) : ℚ :=
  match j.val with
  | 0 => ((-10000:ℚ)/1)*x^5 + ((24000:ℚ)/1)*x^4 + ((-14600:ℚ)/1)*x^3 + ((240:ℚ)/1)*x^2 + ((-101:ℚ)/1)*x^1 + ((19:ℚ)/1)*x^0
  | 1 => ((-25000:ℚ)/1)*x^3 + ((24000:ℚ)/1)*x^2 + ((-2200:ℚ)/1)*x^1 + ((-101:ℚ)/1)*x^0
  | 2 => ((24000:ℚ)/1)*x^1 + ((240:ℚ)/1)*x^0
  | 3 => ((-25000:ℚ)/1)*x^1 + ((-14600:ℚ)/1)*x^0
  | 4 => ((24000:ℚ)/1)*x^0
  | 5 => ((-10000:ℚ)/1)*x^0
  | _ => 0

def monoA (k : Fin 16) : ℚ :=
  match k.val with
  | 0 => ((0:ℚ)/1)
  | 1 => ((0:ℚ)/1)
  | 2 => ((0:ℚ)/1)
  | 3 => ((0:ℚ)/1)
  | 4 => ((0:ℚ)/1)
  | 5 => ((0:ℚ)/1)
  | 6 => ((0:ℚ)/1)
  | 7 => ((0:ℚ)/1)
  | 8 => ((-100:ℚ)/9)
  | 9 => ((1:ℚ)/9)
  | 10 => ((0:ℚ)/1)
  | 11 => ((0:ℚ)/1)
  | 12 => ((0:ℚ)/1)
  | 13 => ((0:ℚ)/1)
  | 14 => ((1:ℚ)/9)
  | 15 => ((4:ℚ)/45)
  | _ => 0

def monoB (k : Fin 16) : ℚ :=
  match k.val with
  | 0 => ((-10000:ℚ)/1)
  | 1 => ((24000:ℚ)/1)
  | 2 => ((-25000:ℚ)/1)
  | 3 => ((-14600:ℚ)/1)
  | 4 => ((24000:ℚ)/1)
  | 5 => ((240:ℚ)/1)
  | 6 => ((-25000:ℚ)/1)
  | 7 => ((24000:ℚ)/1)
  | 8 => ((-2200:ℚ)/1)
  | 9 => ((-101:ℚ)/1)
  | 10 => ((-10000:ℚ)/1)
  | 11 => ((24000:ℚ)/1)
  | 12 => ((-14600:ℚ)/1)
  | 13 => ((240:ℚ)/1)
  | 14 => ((-101:ℚ)/1)
  | 15 => ((19:ℚ)/1)
  | _ => 0

def monoIX (k : Fin 16) : ℕ :=
  match k.val with
  | 0 => 5
  | 1 => 4
  | 2 => 3
  | 3 => 3
  | 4 => 2
  | 5 => 2
  | 6 => 1
  | 7 => 1
  | 8 => 1
  | 9 => 1
  | 10 => 0
  | 11 => 0
  | 12 => 0
  | 13 => 0
  | 14 => 0
  | 15 => 0
  | _ => 0

def monoIY (k : Fin 16) : ℕ :=
  match k.val with
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 0
  | 4 => 1
  | 5 => 0
  | 6 => 3
  | 7 => 2
  | 8 => 1
  | 9 => 0
  | 10 => 5
  | 11 => 4
  | 12 => 3
  | 13 => 2
  | 14 => 1
  | 15 => 0
  | _ => 0

theorem mixed_model (X : ℚ) (y : ℝ) :
    poly (X:ℝ) y = boxPolynomial (aCoeff X) (bCoeff X) (fun _ => 0) (fun j => j.val) (gamma 10) 0 y := by
  unfold poly boxPolynomial
  generalize gamma 10 = g
  norm_num [aCoeff,bCoeff,Fin.sum_univ_succ]
  push_cast
  ring

theorem double_model (x y : ℝ) :
    poly x y = boxPolynomial monoA monoB monoIX monoIY (gamma 10) x y := by
  unfold poly boxPolynomial
  generalize gamma 10 = g
  norm_num [monoA,monoB,monoIX,monoIY,Fin.sum_univ_succ]
  ring

theorem tail_log_rat (y : ℝ) (hy : 0 < y) (hY : y ≤ (tailU:ℝ)) :
    (tailLoRat:ℝ) ≤ y*log (10*y) := by
  have hU : y ≤ 1/31 := by convert hY using 1 <;> norm_num [tailU]
  have h := tail_log y hy hU
  convert h using 1 <;> norm_num [tailLoRat]

theorem mixed_gate : ∀ d : Fin 31, 2 ≤ d.val →
    0 < boxEnvelope (aCoeff (1/(d.val:ℚ))) (bCoeff (1/(d.val:ℚ)))
        (fun _ => 0) (fun j => j.val) gammaLoRat gammaHiRat tailU +
      (1/(d.val:ℚ))*logLoRat d.val+tailLoRat := by
  decide +kernel

theorem double_gate :
    0 < boxEnvelope monoA monoB monoIX monoIY gammaLoRat gammaHiRat tailU+2*tailLoRat := by
  decide +kernel

theorem mixed_compact (d : ℕ) (hd : 2 ≤ d) (hD : d ≤ 30)
    (y : ℝ) (hy : 0 < y) (hY : y ≤ (tailU:ℝ)) :
    0 < poly (1/(d:ℝ)) y+(1/(d:ℝ))*log (10/(d:ℝ))+y*log (10*y) := by
  have hp := boxEnvelope_lower (aCoeff (1/(d:ℚ))) (bCoeff (1/(d:ℚ)))
    (fun _ => 0) (fun j => j.val) gammaLoRat gammaHiRat tailU (gamma 10) 0 y
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
    0 < poly x y+x*log (10*x)+y*log (10*y) := by
  have hp := boxEnvelope_lower monoA monoB monoIX monoIY gammaLoRat gammaHiRat tailU
    (gamma 10) x y gamma_rat_bounds.1 gamma_rat_bounds.2 hx.le hy.le hX hY
  rw [← double_model] at hp
  have hxlog := tail_log_rat x hx hX
  have hylog := tail_log_rat y hy hY
  have hb : (0:ℝ) < (boxEnvelope monoA monoB monoIX monoIY gammaLoRat gammaHiRat tailU:ℝ)+
      2*(tailLoRat:ℝ) := by exact_mod_cast double_gate
  linarith only [hp,hxlog,hylog,hb]

theorem strict_of_nonplane (d c : ℤ) (hd : 1 < d) (hc : 1 < c) (hn : ¬(d=10 ∧ c=10)) :
    0 < edgeCost 10 quadraticAnchor d c := by
  have hd0 : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hc0 : (0:ℝ) < c := by exact_mod_cast (show 0 < c by omega)
  have recip_tail (z : ℤ) (hz : 30 < z) : 1/(z:ℝ) ≤ (tailU:ℝ) := by
    have h : 1/(z:ℝ) ≤ 1/31 := one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast (show 31 ≤ z by omega))
    convert h using 1 <;> norm_num [tailU]
  by_cases hdN : d ≤ 30
  · by_cases hcN : c ≤ 30
    · exact finite_strict d c (by omega) (by omega) hdN hcN hn
    · rw [edge_value d c hd0.ne' hc0.ne']
      have hm := mixed_compact d.toNat (by omega) (by omega) (1/(c:ℝ)) (one_div_pos.mpr hc0) (recip_tail c (by omega))
      have hdc : (d.toNat:ℝ) = d := by exact_mod_cast (Int.toNat_of_nonneg (show 0 ≤ d by omega))
      rw [hdc] at hm
      simpa only [div_eq_mul_inv,one_mul] using hm
  · by_cases hcN : c ≤ 30
    · rw [edgeCost_symm, edge_value c d hc0.ne' hd0.ne']
      have hm := mixed_compact c.toNat (by omega) (by omega) (1/(d:ℝ)) (one_div_pos.mpr hd0) (recip_tail d (by omega))
      have hcc : (c.toNat:ℝ) = c := by exact_mod_cast (Int.toNat_of_nonneg (show 0 ≤ c by omega))
      rw [hcc] at hm
      simpa only [div_eq_mul_inv,one_mul] using hm
    · rw [edge_value d c hd0.ne' hc0.ne']
      simpa only [div_eq_mul_inv,one_mul] using double_compact (1/(d:ℝ)) (1/(c:ℝ))
        (one_div_pos.mpr hd0) (one_div_pos.mpr hc0) (recip_tail d (by omega)) (recip_tail c (by omega))

end SparseComponent.TotalFamily.Density10
