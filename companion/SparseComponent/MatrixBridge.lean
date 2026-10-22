import SparseComponent.LiteralSupport
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

namespace SparseComponent
open Finset Matrix
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

theorem distinctColumns_of_det_ne_zero (A : Matrix ι ι ℤ) (hdet : A.det ≠ 0) :
    DistinctColumns A := by
  intro i j hij
  by_contra hne
  apply hdet
  exact Matrix.det_zero_of_column_eq hne (fun k => congrFun hij k)

/-- The Gram definition is exactly the matrix product `AAᵀ`. -/
theorem gram_eq_mul_transpose (A : Matrix ι ι ℤ) : gram A = A * A.transpose := by
  ext i j
  simp [gram, Matrix.mul_apply, Matrix.transpose_apply]

noncomputable def shiftedMatrix (A : Matrix ι ι ℤ) (r : ℤ) : Matrix ι ι ℤ :=
  (Matrix.of (gram A)) - Matrix.diagonal (fun _ => r - 1)

noncomputable def defectMatrix (A : Matrix ι ι ℤ) (r : ℤ) : Matrix ι ι ℤ :=
  shiftedMatrix A r * (Matrix.diagonal (fun _ => r ^ 2) - (Matrix.of (gram A))) * shiftedMatrix A r

theorem shiftedMatrix_apply (A : Matrix ι ι ℤ) (r : ℤ) (i j : ι) :
    shiftedMatrix A r i j = shiftedColumn A r j i := by
  simp [shiftedMatrix, shiftedColumn, Matrix.diagonal_apply]

theorem shiftedMatrix_symm (A : Matrix ι ι ℤ) (r : ℤ) (i j : ι) :
    shiftedMatrix A r i j = shiftedMatrix A r j i := by
  simp only [shiftedMatrix_apply, shiftedColumn]
  rw [gram_symm]
  by_cases h : i = j
  · simp [h]
  · simp [h, Ne.symm h]

/-- The quadratic local defect is literally the diagonal of the cubic Gram polynomial. -/
theorem localDefect_eq_matrix_diagonal (A : Matrix ι ι ℤ) (r : ℤ) (i : ι) :
    localDefect A r i = defectMatrix A r i i := by
  have hm : ∀ j : ι,
      (((Matrix.diagonal (fun _ : ι => r ^ 2) - (Matrix.of (gram A))) * shiftedMatrix A r) : Matrix ι ι ℤ) j i =
        r ^ 2 * shiftedColumn A r i j - ∑ k, gram A j k * shiftedColumn A r i k := by
    intro j
    simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.diagonal_apply,
      sub_mul, sum_sub_distrib, shiftedMatrix_apply, ite_mul, zero_mul]
    simp
  unfold defectMatrix
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  simp_rw [hm]
  unfold localDefect energy
  apply sum_congr rfl
  intro j hj
  rw [shiftedMatrix_symm, shiftedMatrix_apply]

/-- The trace defect agrees with the exact sum used in integer charging. -/
theorem totalDefect_eq_trace (A : Matrix ι ι ℤ) (r : ℤ) :
    totalDefect A r = Matrix.trace (defectMatrix A r) := by
  unfold totalDefect Matrix.trace Matrix.diag
  apply sum_congr rfl
  exact fun i _ => localDefect_eq_matrix_diagonal A r i

theorem degreeDeficit_eq (A : Matrix ι ι ℤ) (r : ℤ) :
    degreeDeficit A r = r * Fintype.card ι - ∑ i, ∑ j, A i j := by
  unfold degreeDeficit rowDegree
  rw [sum_sub_distrib]
  simp [mul_comm]

/-- Complete nonsingular integer component-stability bridge with literal matrix trace. -/
theorem nonsingular_integer_component_extraction (A : Matrix ι ι ℤ) (hA : Binary A)
    (hdet : A.det ≠ 0) (r : ℤ) (hr : 2 ≤ r)
    (hc : ∀ k, columnDegree A k ≤ r) (hd : ∀ i, rowDegree A i ≤ r) :
    residualRows A r ≤ Matrix.trace (defectMatrix A r) +
      (r ^ 2 - r + 1) * cycleCount A +
      (r * Fintype.card ι - ∑ i, ∑ j, A i j) := by
  simpa only [totalDefect_eq_trace, degreeDeficit_eq] using
    integer_component_extraction A hA (distinctColumns_of_det_ne_zero A hdet) r hr hc hd

end SparseComponent
