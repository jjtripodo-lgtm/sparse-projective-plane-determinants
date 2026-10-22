import SparseComponent.TotalOnes.TotalOnes
import audit.fano_equality.Controls
import audit.total_ones_scalar.Controls

namespace SparseComponent.TotalOnes.FinalControls
open Matrix Finset Real

example (A : Matrix (Fin 0) (Fin 0) ℤ) (hA : Binary A) :
    |(A.det:ℝ)| = exp (0*fanoRate+edgeSlope*((edgeCount A:ℝ)-3*0)) := by
  simpa using (determinant_total_ones_equality_iff 0 A hA).mpr
    (empty_fanoBlockDecomposition A hA)

/-- The theorem applies to an actual row of degree four, exceeding the old cap. -/
def irregularFour : Matrix (Fin 4) (Fin 4) ℤ := fun i j => if i=0 ∨ i=j then 1 else 0

theorem irregularFour_binary : Binary irregularFour := by
  intro i j
  by_cases h : i=0 ∨ i=j
  · right; simp [irregularFour, h]
  · left; simp [irregularFour, h]

theorem irregularFour_degree_four : rowDegree irregularFour 0 = 4 := by decide

theorem irregularFour_ones : edgeCount irregularFour = 7 := by decide

example : |(irregularFour.det:ℝ)| ≤ (24:ℝ)^((4:ℝ)/7) := by
  apply determinant_total_three_ones 4 irregularFour irregularFour_binary
  rw [irregularFour_ones]
  norm_num

example : |(FanoControls.cyclicFano.det:ℝ)| = 24 := FanoControls.cyclicFano_abs_det

example : |(FanoControls.cyclicFano.det:ℝ)| =
    exp ((7:ℝ)*fanoRate+edgeSlope*((edgeCount FanoControls.cyclicFano:ℝ)-3*7)) :=
  (determinant_total_ones_equality_iff 7 FanoControls.cyclicFano FanoControls.cyclicFano_binary).mpr
    FanoControls.cyclicFano_decomposition

end SparseComponent.TotalOnes.FinalControls
