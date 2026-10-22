import SparseComponent.TotalOnes.FanoEquality

namespace SparseComponent.TotalOnes.FanoControls
open Finset Matrix Real
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

/-- Cyclic difference-set incidence matrix for {0,1,3} modulo seven. -/
def cyclicFano : Matrix (Fin 7) (Fin 7) ℤ := fun i j =>
  if (j.val + 7 - i.val) % 7 = 0 ∨ (j.val + 7 - i.val) % 7 = 1 ∨
      (j.val + 7 - i.val) % 7 = 3 then 1 else 0

theorem cyclicFano_binary : Binary cyclicFano := by
  unfold Binary
  decide

theorem cyclicFano_rows : ∀ i, rowDegree cyclicFano i = 3 := by decide

theorem cyclicFano_columns : ∀ j, columnDegree cyclicFano j = 3 := by decide

theorem cyclicFano_gram : ∀ i j, gram cyclicFano i j =
    (if i = j then (2 : ℤ) else 0) + 1 := by decide

theorem cyclicFano_component (i : Fin 7) : component cyclicFano i = univ := by
  ext j
  simp only [mem_component, mem_univ, iff_true]
  apply Relation.ReflTransGen.single
  rw [cyclicFano_gram]
  split_ifs <;> norm_num

theorem cyclicFano_decomposition : FanoBlockDecomposition cyclicFano := by
  apply (fanoBlockDecomposition_iff_all_plane cyclicFano cyclicFano_binary).mpr
  intro i
  rw [cyclicFano_component]
  refine ⟨by norm_num, ?_⟩
  intro j hj k hk
  rw [cyclicFano_gram]
  split_ifs <;> norm_num

theorem cyclicFano_abs_det : |(cyclicFano.det : ℝ)| = 24 := by
  have h := fanoBlockDecomposition_determinant_eq cyclicFano cyclicFano_binary
    cyclicFano_decomposition
  norm_num at h
  exact h

example (A : Matrix (Fin 0) (Fin 0) ℤ) (hA : Binary A) :
    FanoBlockDecomposition A := empty_fanoBlockDecomposition A hA

example (A : Matrix (Fin 0) (Fin 0) ℤ) (hA : Binary A) :
    |(A.det : ℝ)| = exp (0 * fanoRate + edgeSlope * ((edgeCount A : ℝ) - 3 * 0)) := by
  simpa using fanoBlockDecomposition_total_ones_equality A hA
    (empty_fanoBlockDecomposition A hA)

end SparseComponent.TotalOnes.FanoControls
