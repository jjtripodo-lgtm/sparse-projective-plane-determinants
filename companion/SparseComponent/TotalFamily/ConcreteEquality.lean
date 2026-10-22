import SparseComponent.TotalFamily.Density4
import SparseComponent.TotalFamily.Density5
import SparseComponent.TotalFamily.Density6
import SparseComponent.TotalFamily.Equality

namespace SparseComponent.TotalFamily
open Finset Matrix Real TotalOnes

namespace Density4
theorem vertex_zero_degree (d : ℤ) (hd : 2 ≤ d) (u : ℝ) (hu : 0 ≤ u)
    (hz : deficit 4 d u = 0) : (d:ℝ) = 4 := by
  by_contra hn
  have he : d ≠ 4 := by
    intro h
    apply hn
    exact_mod_cast h
  have hneg : negativeGap 4 d u < 0 := by
    by_cases ht : 9 ≤ d
    · exact tail_strict d u (by exact_mod_cast ht) hu
    · interval_cases d <;> norm_num at * <;> first
      | exact degree_2_strict u hu
      | exact degree_3_strict u hu
      | exact degree_5_strict u hu
      | exact degree_6_strict u hu
      | exact degree_7_strict u hu
      | exact degree_8_strict u hu
      | contradiction
  rw [negativeGap_eq_neg_deficit 4 d u (by norm_num), hz] at hneg
  linarith

theorem determinant_total_ones_equality_iff (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) (hA : Binary A) :
    |(A.det:ℝ)| = exp (exponent 4 n (edgeCount A)) ↔
      ∀ i, PlaneRows A 4 (component A i) := by
  exact equality_iff_all_plane_from_vertex_certificate 4 (by norm_num)
    vertex_certificate vertex_zero_degree peeling_margin n A hA

theorem determinant_total_budget_equality_iff (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : Binary A) (he : edgeCount A ≤ 4*(n:ℤ)) :
    |(A.det:ℝ)| = exp ((n:ℝ)*rate 4) ↔ ∀ i, PlaneRows A 4 (component A i) := by
  constructor
  · intro heq
    have hup : exp (exponent 4 n (edgeCount A)) ≤ exp ((n:ℝ)*rate 4) := by
      apply exp_le_exp.mpr
      unfold exponent
      have hbudget : (edgeCount A:ℝ)-4*(n:ℝ) ≤ 0 := by exact_mod_cast sub_nonpos.mpr he
      have ht := mul_nonpos_of_nonneg_of_nonpos (slope_pos 4 (by norm_num)).le hbudget
      linarith
    rw [← heq] at hup
    exact (determinant_total_ones_equality_iff n A hA).mp
      (le_antisymm (determinant_total_ones n A hA) hup)
  · intro hp
    have hd := all_plane_rowDegree A hA 4 hp
    have hedge : edgeCount A = 4*(n:ℤ) := by simp [edgeCount, hd]; ring
    have h := (determinant_total_ones_equality_iff n A hA).mpr hp
    simpa [exponent, hedge] using h
end Density4

namespace Density5
theorem vertex_zero_degree (d : ℤ) (hd : 2 ≤ d) (u : ℝ) (hu : 0 ≤ u)
    (hz : deficit 5 d u = 0) : (d:ℝ) = 5 := by
  by_contra hn
  have he : d ≠ 5 := by
    intro h
    apply hn
    exact_mod_cast h
  have hneg : negativeGap 5 d u < 0 := by
    by_cases ht : 10 ≤ d
    · exact tail_strict d u (by exact_mod_cast ht) hu
    · interval_cases d <;> norm_num at * <;> first
      | exact degree_2_strict u hu
      | exact degree_3_strict u hu
      | exact degree_4_strict u hu
      | exact degree_6_strict u hu
      | exact degree_7_strict u hu
      | exact degree_8_strict u hu
      | exact degree_9_strict u hu
      | contradiction
  rw [negativeGap_eq_neg_deficit 5 d u (by norm_num), hz] at hneg
  linarith

theorem determinant_total_ones_equality_iff (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) (hA : Binary A) :
    |(A.det:ℝ)| = exp (exponent 5 n (edgeCount A)) ↔
      ∀ i, PlaneRows A 5 (component A i) := by
  exact equality_iff_all_plane_from_vertex_certificate 5 (by norm_num)
    vertex_certificate vertex_zero_degree peeling_margin n A hA

theorem determinant_total_budget_equality_iff (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : Binary A) (he : edgeCount A ≤ 5*(n:ℤ)) :
    |(A.det:ℝ)| = exp ((n:ℝ)*rate 5) ↔ ∀ i, PlaneRows A 5 (component A i) := by
  constructor
  · intro heq
    have hup : exp (exponent 5 n (edgeCount A)) ≤ exp ((n:ℝ)*rate 5) := by
      apply exp_le_exp.mpr
      unfold exponent
      have hbudget : (edgeCount A:ℝ)-5*(n:ℝ) ≤ 0 := by exact_mod_cast sub_nonpos.mpr he
      have ht := mul_nonpos_of_nonneg_of_nonpos (slope_pos 5 (by norm_num)).le hbudget
      linarith
    rw [← heq] at hup
    exact (determinant_total_ones_equality_iff n A hA).mp
      (le_antisymm (determinant_total_ones n A hA) hup)
  · intro hp
    have hd := all_plane_rowDegree A hA 5 hp
    have hedge : edgeCount A = 5*(n:ℤ) := by simp [edgeCount, hd]; ring
    have h := (determinant_total_ones_equality_iff n A hA).mpr hp
    simpa [exponent, hedge] using h
end Density5

namespace Density6
theorem vertex_zero_degree (d : ℤ) (hd : 2 ≤ d) (u : ℝ) (hu : 0 ≤ u)
    (hz : deficit 6 d u = 0) : (d:ℝ) = 6 := by
  by_contra hn
  have he : d ≠ 6 := by
    intro h
    apply hn
    exact_mod_cast h
  have hneg : negativeGap 6 d u < 0 := by
    by_cases ht : 12 ≤ d
    · exact tail_strict d u (by exact_mod_cast ht) hu
    · interval_cases d <;> norm_num at * <;> first
      | exact degree_2_strict u hu
      | exact degree_3_strict u hu
      | exact degree_4_strict u hu
      | exact degree_5_strict u hu
      | exact degree_7_strict u hu
      | exact degree_8_strict u hu
      | exact degree_9_strict u hu
      | exact degree_10_strict u hu
      | exact degree_11_strict u hu
      | contradiction
  rw [negativeGap_eq_neg_deficit 6 d u (by norm_num), hz] at hneg
  linarith

theorem determinant_total_ones_equality_iff (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) (hA : Binary A) :
    |(A.det:ℝ)| = exp (exponent 6 n (edgeCount A)) ↔
      ∀ i, PlaneRows A 6 (component A i) := by
  exact equality_iff_all_plane_from_vertex_certificate 6 (by norm_num)
    vertex_certificate vertex_zero_degree peeling_margin n A hA

theorem determinant_total_budget_equality_iff (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : Binary A) (he : edgeCount A ≤ 6*(n:ℤ)) :
    |(A.det:ℝ)| = exp ((n:ℝ)*rate 6) ↔ ∀ i, PlaneRows A 6 (component A i) := by
  constructor
  · intro heq
    have hup : exp (exponent 6 n (edgeCount A)) ≤ exp ((n:ℝ)*rate 6) := by
      apply exp_le_exp.mpr
      unfold exponent
      have hbudget : (edgeCount A:ℝ)-6*(n:ℝ) ≤ 0 := by exact_mod_cast sub_nonpos.mpr he
      have ht := mul_nonpos_of_nonneg_of_nonpos (slope_pos 6 (by norm_num)).le hbudget
      linarith
    rw [← heq] at hup
    exact (determinant_total_ones_equality_iff n A hA).mp
      (le_antisymm (determinant_total_ones n A hA) hup)
  · intro hp
    have hd := all_plane_rowDegree A hA 6 hp
    have hedge : edgeCount A = 6*(n:ℤ) := by simp [edgeCount, hd]; ring
    have h := (determinant_total_ones_equality_iff n A hA).mpr hp
    simpa [exponent, hedge] using h
end Density6

end SparseComponent.TotalFamily
