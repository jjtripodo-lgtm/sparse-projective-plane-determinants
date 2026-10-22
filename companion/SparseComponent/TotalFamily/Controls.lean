import SparseComponent.TotalFamily.Interface

namespace SparseComponent.TotalFamily.Controls
open Finset Matrix Real TotalOnes

def irregularSeven : Matrix (Fin 7) (Fin 7) ℤ := fun i j => if i=0 ∨ i=j then 1 else 0

theorem irregularSeven_binary : Binary irregularSeven := by
  intro i j
  by_cases h : i=0 ∨ i=j
  · right; simp [irregularSeven, h]
  · left; simp [irregularSeven, h]

theorem irregularSeven_degree : rowDegree irregularSeven 0 = 7 := by decide
theorem irregularSeven_ones : edgeCount irregularSeven = 13 := by decide

theorem irregularSeven_det : irregularSeven.det = 1 := by
  have ht : irregularSeven.BlockTriangular id := by
    intro i j hij
    have hi : i ≠ 0 := by intro he; subst i; simp at hij
    have hne : i ≠ j := by simpa using (ne_of_gt hij)
    simp [irregularSeven, hi, hne]
  rw [Matrix.det_of_upperTriangular ht]
  simp [irregularSeven]

/-- A nonsingular actual matrix with row degree seven is admitted by all three budget endpoints. -/
theorem high_degree_control :
    |(irregularSeven.det:ℝ)| ≤ (2916:ℝ)^((7:ℝ)/13) ∧
    |(irregularSeven.det:ℝ)| ≤ (5242880:ℝ)^((7:ℝ)/21) ∧
    |(irregularSeven.det:ℝ)| ≤ (183105468750:ℝ)^((7:ℝ)/31) := by
  refine ⟨literal_density_four 7 irregularSeven irregularSeven_binary ?_,
    literal_density_five 7 irregularSeven irregularSeven_binary ?_,
    literal_density_six 7 irregularSeven irregularSeven_binary ?_⟩ <;>
    change edgeCount irregularSeven ≤ _ <;> rw [irregularSeven_ones] <;> norm_num

example (A : Matrix (Fin 0) (Fin 0) ℤ) (hA : Binary A) :
    |(A.det:ℝ)| = exp (exponent 4 0 (edgeCount A)) := by
  apply (Density4.determinant_total_ones_equality_iff 0 A hA).mpr
  intro i
  exact Fin.elim0 i

example : |((0 : Matrix (Fin 3) (Fin 3) ℤ).det:ℝ)| ≤ (2916:ℝ)^((3:ℝ)/13) := by
  apply literal_density_four
  · intro i j; left; rfl
  · norm_num
end SparseComponent.TotalFamily.Controls
