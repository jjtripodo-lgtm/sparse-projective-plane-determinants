import SparseComponent.TotalFamily.Density7.TailScalar

namespace SparseComponent.TotalFamily.Density7
open Finset Matrix Real TotalOnes
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

theorem strict_of_nonplane (d c : ℤ) (hd : 1 < d) (hc : 1 < c) (hn : ¬(d=7 ∧ c=7)) :
    0 < edgeCost 7 (linearAnchor 7) d c := by
  have hd0 : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hc0 : (0:ℝ) < c := by exact_mod_cast (show 0 < c by omega)
  by_cases hdN : d ≤ 21
  · by_cases hcN : c ≤ 21
    · exact finite_strict d c (by omega) (by omega) hdN hcN hn
    · rw [edge_value d c hd0.ne' hc0.ne']
      have hC : 1/(c:ℝ) ≤ 1/22 := one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast (show 22 ≤ c by omega))
      have hp := one_div_pos.mpr hc0
      interval_cases d <;> simp only [Int.cast_ofNat]
      · simpa only [div_eq_mul_inv, one_mul] using mixed_2 (1/(c:ℝ)) hp hC
      · simpa only [div_eq_mul_inv, one_mul] using mixed_3 (1/(c:ℝ)) hp hC
      · simpa only [div_eq_mul_inv, one_mul] using mixed_4 (1/(c:ℝ)) hp hC
      · simpa only [div_eq_mul_inv, one_mul] using mixed_5 (1/(c:ℝ)) hp hC
      · simpa only [div_eq_mul_inv, one_mul] using mixed_6 (1/(c:ℝ)) hp hC
      · simpa only [div_eq_mul_inv, one_mul] using mixed_7 (1/(c:ℝ)) hp hC
      · simpa only [div_eq_mul_inv, one_mul] using mixed_8 (1/(c:ℝ)) hp hC
      · simpa only [div_eq_mul_inv, one_mul] using mixed_9 (1/(c:ℝ)) hp hC
      · simpa only [div_eq_mul_inv, one_mul] using mixed_10 (1/(c:ℝ)) hp hC
      · simpa only [div_eq_mul_inv, one_mul] using mixed_11 (1/(c:ℝ)) hp hC
      · simpa only [div_eq_mul_inv, one_mul] using mixed_12 (1/(c:ℝ)) hp hC
      · simpa only [div_eq_mul_inv, one_mul] using mixed_13 (1/(c:ℝ)) hp hC
      · simpa only [div_eq_mul_inv, one_mul] using mixed_14 (1/(c:ℝ)) hp hC
      · simpa only [div_eq_mul_inv, one_mul] using mixed_15 (1/(c:ℝ)) hp hC
      · simpa only [div_eq_mul_inv, one_mul] using mixed_16 (1/(c:ℝ)) hp hC
      · simpa only [div_eq_mul_inv, one_mul] using mixed_17 (1/(c:ℝ)) hp hC
      · simpa only [div_eq_mul_inv, one_mul] using mixed_18 (1/(c:ℝ)) hp hC
      · simpa only [div_eq_mul_inv, one_mul] using mixed_19 (1/(c:ℝ)) hp hC
      · simpa only [div_eq_mul_inv, one_mul] using mixed_20 (1/(c:ℝ)) hp hC
      · simpa only [div_eq_mul_inv, one_mul] using mixed_21 (1/(c:ℝ)) hp hC
  · by_cases hcN : c ≤ 21
    · rw [edgeCost_symm]
      rw [edge_value c d hc0.ne' hd0.ne']
      have hD : 1/(d:ℝ) ≤ 1/22 := one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast (show 22 ≤ d by omega))
      have hp := one_div_pos.mpr hd0
      interval_cases c <;> simp only [Int.cast_ofNat]
      · simpa only [div_eq_mul_inv, one_mul] using mixed_2 (1/(d:ℝ)) hp hD
      · simpa only [div_eq_mul_inv, one_mul] using mixed_3 (1/(d:ℝ)) hp hD
      · simpa only [div_eq_mul_inv, one_mul] using mixed_4 (1/(d:ℝ)) hp hD
      · simpa only [div_eq_mul_inv, one_mul] using mixed_5 (1/(d:ℝ)) hp hD
      · simpa only [div_eq_mul_inv, one_mul] using mixed_6 (1/(d:ℝ)) hp hD
      · simpa only [div_eq_mul_inv, one_mul] using mixed_7 (1/(d:ℝ)) hp hD
      · simpa only [div_eq_mul_inv, one_mul] using mixed_8 (1/(d:ℝ)) hp hD
      · simpa only [div_eq_mul_inv, one_mul] using mixed_9 (1/(d:ℝ)) hp hD
      · simpa only [div_eq_mul_inv, one_mul] using mixed_10 (1/(d:ℝ)) hp hD
      · simpa only [div_eq_mul_inv, one_mul] using mixed_11 (1/(d:ℝ)) hp hD
      · simpa only [div_eq_mul_inv, one_mul] using mixed_12 (1/(d:ℝ)) hp hD
      · simpa only [div_eq_mul_inv, one_mul] using mixed_13 (1/(d:ℝ)) hp hD
      · simpa only [div_eq_mul_inv, one_mul] using mixed_14 (1/(d:ℝ)) hp hD
      · simpa only [div_eq_mul_inv, one_mul] using mixed_15 (1/(d:ℝ)) hp hD
      · simpa only [div_eq_mul_inv, one_mul] using mixed_16 (1/(d:ℝ)) hp hD
      · simpa only [div_eq_mul_inv, one_mul] using mixed_17 (1/(d:ℝ)) hp hD
      · simpa only [div_eq_mul_inv, one_mul] using mixed_18 (1/(d:ℝ)) hp hD
      · simpa only [div_eq_mul_inv, one_mul] using mixed_19 (1/(d:ℝ)) hp hD
      · simpa only [div_eq_mul_inv, one_mul] using mixed_20 (1/(d:ℝ)) hp hD
      · simpa only [div_eq_mul_inv, one_mul] using mixed_21 (1/(d:ℝ)) hp hD
    · rw [edge_value d c hd0.ne' hc0.ne']
      have hD : 1/(d:ℝ) ≤ 1/22 := one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast (show 22 ≤ d by omega))
      have hC : 1/(c:ℝ) ≤ 1/22 := one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast (show 22 ≤ c by omega))
      simpa only [div_eq_mul_inv, one_mul] using double_tail (1/(d:ℝ)) (1/(c:ℝ)) (one_div_pos.mpr hd0) (one_div_pos.mpr hc0) hD hC

end SparseComponent.TotalFamily.Density7
