import SparseComponent.TotalOnes.MinimumDegree
import SparseComponent.TotalOnes.LaplacePeeling
import SparseComponent.TotalOnes.FanoEquality

namespace SparseComponent.TotalOnes
open Finset Matrix Real

/-- The full total-ones estimate, with no degree or spectral cap on the original matrix. -/
theorem determinant_total_ones (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) (hA : Binary A) :
    |(A.det:ℝ)| ≤ exp ((n:ℝ)*fanoRate+edgeSlope*((edgeCount A:ℝ)-3*(n:ℝ))) := by
  apply conditional_all_orders_bound (fun m B hB hdet hd hc => ?_) n A hA
  simpa only [Fintype.card_fin] using minimum_degree_bound B hB hdet hd hc

theorem determinant_total_ones_equality_regular (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℤ) (hA : Binary A)
    (he : |(A.det:ℝ)| = exp ((n:ℝ)*fanoRate+edgeSlope*((edgeCount A:ℝ)-3*(n:ℝ)))) :
    (∀ i, rowDegree A i = 3) ∧ (∀ j, columnDegree A j = 3) := by
  apply conditional_all_orders_equality_regularity
    (fun m B hB hdet hd hc => ?_) (fun m B hB hdet hd hc hEq => ?_) n A hA he
  · simpa only [Fintype.card_fin] using minimum_degree_bound B hB hdet hd hc
  · apply minimum_degree_equality_regular B hB hdet hd hc
    simpa only [Fintype.card_fin] using hEq

/-- Equality is precisely a disjoint union of actual isolated Fano incidence blocks. -/
theorem determinant_total_ones_equality_iff (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℤ) (hA : Binary A) :
    |(A.det:ℝ)| = exp ((n:ℝ)*fanoRate+edgeSlope*((edgeCount A:ℝ)-3*(n:ℝ))) ↔
      FanoBlockDecomposition A := by
  constructor
  · intro he
    obtain ⟨hd,hc⟩ := determinant_total_ones_equality_regular n A hA he
    apply (total_ones_equality_iff_fano_of_regular A hA hd hc).mp
    simpa only [Fintype.card_fin] using he
  · intro hF
    simpa only [Fintype.card_fin] using fanoBlockDecomposition_total_ones_equality A hA hF

theorem exp_total_ones_le_fano (n : ℕ) (e : ℤ) (he : e ≤ 3*(n:ℤ)) :
    exp ((n:ℝ)*fanoRate+edgeSlope*((e:ℝ)-3*(n:ℝ))) ≤ (24:ℝ)^((n:ℝ)/7) := by
  rw [← exp_card_fanoRate]
  apply exp_le_exp.mpr
  have hbudget : (e:ℝ)-3*(n:ℝ) ≤ 0 := by exact_mod_cast sub_nonpos.mpr he
  have hterm := mul_nonpos_of_nonneg_of_nonpos edgeSlope_pos.le hbudget
  linarith

/-- The full total-3n Fano determinant bound, including empty and singular matrices. -/
theorem determinant_total_three_ones (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : Binary A) (he : edgeCount A ≤ 3*(n:ℤ)) :
    |(A.det:ℝ)| ≤ (24:ℝ)^((n:ℝ)/7) :=
  (determinant_total_ones n A hA).trans (exp_total_ones_le_fano n (edgeCount A) he)

theorem determinant_total_three_ones_equality_iff (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℤ) (hA : Binary A) (he : edgeCount A ≤ 3*(n:ℤ)) :
    |(A.det:ℝ)| = (24:ℝ)^((n:ℝ)/7) ↔ FanoBlockDecomposition A := by
  constructor
  · intro hEq
    have hu := exp_total_ones_le_fano n (edgeCount A) he
    rw [← hEq] at hu
    exact (determinant_total_ones_equality_iff n A hA).mp
      (le_antisymm (determinant_total_ones n A hA) hu)
  · intro hF
    simpa only [Fintype.card_fin] using fanoBlockDecomposition_determinant_eq A hA hF

/-- Source-literal consumer: only the original binary integer entries are assumed. -/
theorem determinant_total_ones_literal (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : ∀ i j, A i j = 0 ∨ A i j = 1) :
    |(A.det:ℝ)| ≤ exp ((n:ℝ)*(log 24/7)+
      (1/12+5*(((7:ℝ)/2-log (9/2))/49)/2)*
      ((((∑ i, ∑ j, A i j):ℤ):ℝ)-3*(n:ℝ))) := by
  simpa only [fanoRate, edgeSlope, curvature, edgeCount, rowDegree]
    using determinant_total_ones n A hA

end SparseComponent.TotalOnes
