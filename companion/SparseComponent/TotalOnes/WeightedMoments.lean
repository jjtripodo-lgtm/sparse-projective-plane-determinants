import SparseComponent.TotalOnes.MatrixDefs
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.BigOperators.Field

/-!
The weighted moment estimate uses the actual entries of the degree-normalized
matrix. The elementary fourth-moment bound keeps equal-row contributions exactly
and discards only nonnegative unequal-row cross terms. The entry fourth powers
are then bounded by an edgewise squared-difference identity.
-/

namespace SparseComponent.TotalOnes
open Finset Matrix
variable {ι : Type*} [Fintype ι]

private theorem wm_rowSize_pos (A : Matrix ι ι ℤ)
    (hd : ∀ i, 0 < rowDegree A i) (i : ι) : 0 < rowSize A i := by
  unfold rowSize
  exact_mod_cast hd i

private theorem wm_columnSize_pos (A : Matrix ι ι ℤ)
    (hc : ∀ j, 0 < columnDegree A j) (j : ι) : 0 < columnSize A j := by
  unfold columnSize
  exact_mod_cast hc j

theorem rowMass_nonneg (A : Matrix ι ι ℤ) (hA : Binary A)
    (hd : ∀ i, 0 < rowDegree A i) (hc : ∀ j, 0 < columnDegree A j) (i : ι) :
    0 ≤ rowMass A i := by
  apply sum_nonneg
  intro j _
  exact div_nonneg (by exact_mod_cast binary_nonneg A hA i j)
    (mul_nonneg (wm_rowSize_pos A hd i).le (wm_columnSize_pos A hc j).le)

theorem columnMass_nonneg (A : Matrix ι ι ℤ) (hA : Binary A)
    (hd : ∀ i, 0 < rowDegree A i) (hc : ∀ j, 0 < columnDegree A j) (j : ι) :
    0 ≤ columnMass A j := by
  apply sum_nonneg
  intro i _
  exact div_nonneg (by exact_mod_cast binary_nonneg A hA i j)
    (mul_nonneg (wm_rowSize_pos A hd i).le (wm_columnSize_pos A hc j).le)

theorem sum_rowMass_eq_columnMass (A : Matrix ι ι ℤ) :
    (∑ i, rowMass A i) = ∑ j, columnMass A j := by
  exact sum_comm

theorem weighted_row_balance (A : Matrix ι ι ℤ)
    (hd : ∀ i, 0 < rowDegree A i) (hc : ∀ j, 0 < columnDegree A j) :
    (∑ i, rowSize A i * rowMass A i) = (Fintype.card ι : ℝ) := by
  have ht (i j : ι) : rowSize A i * ((A i j : ℝ) /
      (rowSize A i * columnSize A j)) = (A i j : ℝ) / columnSize A j := by
    have hi := ne_of_gt (wm_rowSize_pos A hd i)
    field_simp
  simp_rw [rowMass, mul_sum, ht]
  rw [sum_comm]
  simp_rw [← sum_div, show ∀ j, (∑ i, (A i j : ℝ)) = columnSize A j by
    intro j; simp [columnSize, columnDegree]]
  simp [div_self (ne_of_gt (wm_columnSize_pos A hc _))]

theorem weighted_column_balance (A : Matrix ι ι ℤ)
    (hd : ∀ i, 0 < rowDegree A i) (hc : ∀ j, 0 < columnDegree A j) :
    (∑ j, columnSize A j * columnMass A j) = (Fintype.card ι : ℝ) := by
  have ht (i j : ι) : columnSize A j * ((A i j : ℝ) /
      (rowSize A i * columnSize A j)) = (A i j : ℝ) / rowSize A i := by
    have hj := ne_of_gt (wm_columnSize_pos A hc j)
    field_simp
  simp_rw [columnMass, mul_sum, ht]
  rw [sum_comm]
  simp_rw [← sum_div, show ∀ i, (∑ j, (A i j : ℝ)) = rowSize A i by
    intro i; simp [rowSize, rowDegree]]
  simp [div_self (ne_of_gt (wm_rowSize_pos A hd _))]

theorem normalizedMatrix_sq (A : Matrix ι ι ℤ) (hA : Binary A)
    (hd : ∀ i, 0 < rowDegree A i) (hc : ∀ j, 0 < columnDegree A j) (i j : ι) :
    normalizedMatrix A i j ^ 2 = (A i j : ℝ) / (rowSize A i * columnSize A j) := by
  unfold normalizedMatrix
  rw [div_pow, mul_pow, Real.sq_sqrt (wm_rowSize_pos A hd i).le,
    Real.sq_sqrt (wm_columnSize_pos A hc j).le]
  rcases hA i j with h | h <;> simp [h]

theorem normalizedMatrix_row_sq_sum (A : Matrix ι ι ℤ) (hA : Binary A)
    (hd : ∀ i, 0 < rowDegree A i) (hc : ∀ j, 0 < columnDegree A j) (i : ι) :
    (∑ j, normalizedMatrix A i j ^ 2) = rowMass A i := by
  simp_rw [normalizedMatrix_sq A hA hd hc]
  rfl

theorem normalizedMatrix_column_sq_sum (A : Matrix ι ι ℤ) (hA : Binary A)
    (hd : ∀ i, 0 < rowDegree A i) (hc : ∀ j, 0 < columnDegree A j) (j : ι) :
    (∑ i, normalizedMatrix A i j ^ 2) = columnMass A j := by
  simp_rw [normalizedMatrix_sq A hA hd hc]
  rfl

theorem normalizedGram_trace (A : Matrix ι ι ℤ) (hA : Binary A)
    (hd : ∀ i, 0 < rowDegree A i) (hc : ∀ j, 0 < columnDegree A j) :
    Matrix.trace (normalizedGram A) = 9 * ∑ i, rowMass A i := by
  rw [normalizedGram, Matrix.trace_smul]
  change 9 * (∑ i, ∑ j, normalizedMatrix A i j * normalizedMatrix A i j) = _
  simp_rw [← pow_two, normalizedMatrix_row_sq_sum A hA hd hc]

/-- The fourth moment of any nonnegative real matrix dominates both squared
row and column masses, with the twice-counted entry fourth powers removed. -/
theorem nonnegative_matrix_fourth_moment_lower (M : Matrix ι ι ℝ)
    (hM : ∀ i j, 0 ≤ M i j) :
    (∑ i, (∑ j, M i j ^ 2) ^ 2) + (∑ j, (∑ i, M i j ^ 2) ^ 2) -
      (∑ i, ∑ j, M i j ^ 4) ≤
        Matrix.trace ((M * M.transpose) * (M * M.transpose)) := by
  classical
  have hp (i k : ι) :
      (if i = k then (∑ j, M i j ^ 2) ^ 2 else 0) +
        (∑ j, M i j ^ 2 * M k j ^ 2) ≤
      (∑ j, M i j * M k j) ^ 2 +
        (if i = k then ∑ j, M i j ^ 4 else 0) := by
    by_cases hik : i = k
    · subst k
      simp only [ite_true, ← pow_two]
      have he : (∑ j, (M i j ^ 2) ^ 2) = ∑ j, M i j ^ 4 := by
        apply sum_congr rfl
        intro j _
        ring
      rw [he]
    · simp only [hik, ite_false, zero_add, add_zero]
      simpa only [mul_pow] using sum_sq_le_sq_sum_of_nonneg
        (s := (univ : Finset ι)) (f := fun j => M i j * M k j)
        (fun j _ => mul_nonneg (hM i j) (hM k j))
  have hs := sum_le_sum (s := (univ : Finset ι)) fun i _ =>
    sum_le_sum (s := (univ : Finset ι)) fun k _ => hp i k
  simp only [sum_add_distrib] at hs
  simp only [sum_ite_eq, mem_univ, if_true] at hs
  have hc : (∑ i, ∑ k, ∑ j, M i j ^ 2 * M k j ^ 2) =
      ∑ j, (∑ i, M i j ^ 2) ^ 2 := by
    rw [sum_comm]
    conv_lhs => arg 2; ext k; rw [sum_comm]
    rw [sum_comm]
    apply sum_congr rfl
    intro j _
    rw [pow_two, sum_mul_sum]
    exact sum_comm
  have ht : Matrix.trace ((M * M.transpose) * (M * M.transpose)) =
      ∑ i, ∑ k, (∑ j, M i j * M k j) ^ 2 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro k _
    have he : (∑ j, M k j * M i j) = ∑ j, M i j * M k j := by
      apply sum_congr rfl
      intro j _
      ring
    rw [he, pow_two]
  rw [hc] at hs
  rw [ht]
  linarith

private theorem reciprocal_edge_fourth_le (d c : ℝ) (hd : 0 < d) (hc : 0 < c) :
    (1 / (d * c)) ^ 2 ≤ (1 / (d * c) / d ^ 2 + 1 / (d * c) / c ^ 2) / 2 := by
  have hd0 := ne_of_gt hd
  have hc0 := ne_of_gt hc
  have he : (1 / (d * c) / d ^ 2 + 1 / (d * c) / c ^ 2) / 2 -
      (1 / (d * c)) ^ 2 = (d - c) ^ 2 / (2 * d ^ 3 * c ^ 3) := by
    field_simp
    ring
  have hn : 0 ≤ (d - c) ^ 2 / (2 * d ^ 3 * c ^ 3) :=
    div_nonneg (sq_nonneg _) (by positivity)
  linarith

theorem normalizedMatrix_fourth_le (A : Matrix ι ι ℤ) (hA : Binary A)
    (hd : ∀ i, 0 < rowDegree A i) (hc : ∀ j, 0 < columnDegree A j) (i j : ι) :
    normalizedMatrix A i j ^ 4 ≤
      (((A i j : ℝ) / (rowSize A i * columnSize A j)) / rowSize A i ^ 2 +
       ((A i j : ℝ) / (rowSize A i * columnSize A j)) / columnSize A j ^ 2) / 2 := by
  rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, normalizedMatrix_sq A hA hd hc]
  rcases hA i j with h | h
  · simp [h]
  · simp only [h, Int.cast_one]
    exact reciprocal_edge_fourth_le _ _ (wm_rowSize_pos A hd i) (wm_columnSize_pos A hc j)

theorem normalizedMatrix_fourth_sum_le (A : Matrix ι ι ℤ) (hA : Binary A)
    (hd : ∀ i, 0 < rowDegree A i) (hc : ∀ j, 0 < columnDegree A j) :
    (∑ i, ∑ j, normalizedMatrix A i j ^ 4) ≤
      ((∑ i, rowMass A i / rowSize A i ^ 2) +
       (∑ j, columnMass A j / columnSize A j ^ 2)) / 2 := by
  have h := sum_le_sum (s := (univ : Finset ι)) fun i _ =>
    sum_le_sum (s := (univ : Finset ι)) fun j _ => normalizedMatrix_fourth_le A hA hd hc i j
  have half_sum (f : ι → ℝ) : (∑ i, f i / 2) = (∑ i, f i) / 2 :=
    (sum_div univ f 2).symm
  simp only [half_sum, sum_add_distrib] at h
  have hr : (∑ i, ∑ j, (A i j : ℝ) / (rowSize A i * columnSize A j) / rowSize A i ^ 2) =
      ∑ i, rowMass A i / rowSize A i ^ 2 := by simp only [rowMass, sum_div]
  have hc' : (∑ i, ∑ j, (A i j : ℝ) / (rowSize A i * columnSize A j) / columnSize A j ^ 2) =
      ∑ j, columnMass A j / columnSize A j ^ 2 := by
    rw [sum_comm]
    simp only [columnMass, sum_div]
  rw [hr, hc'] at h
  exact h

/-- The actual weighted second-moment estimate. No rectangle count, trace bound,
balance condition, or degree cap is supplied as a premise. -/
theorem normalizedGram_second_moment_lower (A : Matrix ι ι ℤ) (hA : Binary A)
    (hd : ∀ i, 0 < rowDegree A i) (hc : ∀ j, 0 < columnDegree A j) :
    81 * ((∑ i, rowMass A i ^ 2) + (∑ j, columnMass A j ^ 2) -
      ((∑ i, rowMass A i / rowSize A i ^ 2) +
       (∑ j, columnMass A j / columnSize A j ^ 2)) / 2) ≤
      Matrix.trace (normalizedGram A * normalizedGram A) := by
  have hn (i j : ι) : 0 ≤ normalizedMatrix A i j :=
    div_nonneg (by exact_mod_cast binary_nonneg A hA i j)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have h := nonnegative_matrix_fourth_moment_lower (normalizedMatrix A) hn
  simp_rw [normalizedMatrix_row_sq_sum A hA hd hc,
    normalizedMatrix_column_sq_sum A hA hd hc] at h
  have hq := normalizedMatrix_fourth_sum_le A hA hd hc
  have ht : Matrix.trace (normalizedGram A * normalizedGram A) =
      81 * Matrix.trace ((normalizedMatrix A * (normalizedMatrix A).transpose) *
        (normalizedMatrix A * (normalizedMatrix A).transpose)) := by
    simp only [normalizedGram, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, Matrix.trace_smul, smul_eq_mul]
    norm_num
  rw [ht]
  linarith

end SparseComponent.TotalOnes
