import SparseComponent.MatrixBridge

namespace SparseComponent
open Finset Matrix
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

theorem chooseTwo_identity (b : ℤ) : 2 * chooseTwo b = b * (b - 1) :=
  Int.mul_ediv_cancel' (Int.even_mul_pred_self b).two_dvd

theorem gram_square_entry (A : ι → ι → ℤ) (hA : Binary A) (i j : ι) :
    gram A i j ^ 2 =
      (if i = j then rowDegree A i ^ 2 - rowDegree A i else 0) +
      gram A i j + 2 * cycleWeight A i j + 2 * cycleWeight A j i := by
  by_cases h : i = j
  · subst j
    simp [gram_diagonal A hA, cycleWeight]
  · rw [if_neg h]
    rcases lt_or_gt_of_ne h with hij | hji
    · rw [cycleWeight, if_pos hij, cycleWeight, if_neg (not_lt.mpr hij.le), mul_zero]
      have := chooseTwo_identity (gram A i j)
      nlinarith
    · rw [cycleWeight, if_neg (not_lt.mpr hji.le), cycleWeight, if_pos hji, mul_zero, gram_symm A j i]
      have := chooseTwo_identity (gram A i j)
      nlinarith

theorem sum_gram_eq_column_squares (A : ι → ι → ℤ) :
    (∑ i, ∑ j, gram A i j) = ∑ k, columnDegree A k ^ 2 := by
  change (∑ i, rowSum (gram A) i) = _
  simp_rw [gram_rowSum]
  rw [sum_comm]
  apply sum_congr rfl
  intro k hk
  rw [← sum_mul]
  change columnDegree A k * columnDegree A k = _
  ring

theorem sum_gram_squares (A : ι → ι → ℤ) (hA : Binary A) :
    (∑ i, ∑ j, gram A i j ^ 2) =
      (∑ i, rowDegree A i ^ 2) + (∑ k, columnDegree A k ^ 2) -
      (∑ i, rowDegree A i) + 4 * cycleCount A := by
  simp_rw [gram_square_entry A hA]
  simp only [sum_add_distrib, sum_ite_eq, mem_univ, if_true, sum_sub_distrib, ← mul_sum]
  have hc : (∑ i, ∑ j, cycleWeight A j i) = cycleCount A := by
    rw [sum_comm]
    rfl
  rw [hc, sum_gram_eq_column_squares]
  unfold cycleCount
  ring

theorem trace_gram_square (A : Matrix ι ι ℤ) (hA : Binary A) :
    Matrix.trace ((Matrix.of (gram A)) * (Matrix.of (gram A))) =
      (∑ i, rowDegree A i ^ 2) + (∑ k, columnDegree A k ^ 2) -
      (∑ i, rowDegree A i) + 4 * cycleCount A := by
  rw [← sum_gram_squares A hA]
  unfold Matrix.trace Matrix.diag
  apply sum_congr rfl
  intro i hi
  rw [Matrix.mul_apply]
  apply sum_congr rfl
  intro j hj
  simp only [Matrix.of_apply, gram_symm A j i, pow_two]

theorem row_column_degree_sum (A : ι → ι → ℤ) :
    (∑ i, rowDegree A i) = ∑ k, columnDegree A k := by
  unfold rowDegree columnDegree
  exact sum_comm

theorem degree_squares_lower (d : ι → ℤ) (r : ℤ) :
    2 * r * (∑ i, d i) - Fintype.card ι * r ^ 2 ≤ ∑ i, d i ^ 2 := by
  have h : 0 ≤ ∑ i, (d i - r) ^ 2 := sum_nonneg fun i _ => sq_nonneg _
  simp_rw [show ∀ i, (d i - r) ^ 2 = d i ^ 2 - 2 * r * d i + r ^ 2 by intro i; ring] at h
  simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, nsmul_eq_mul, card_univ] at h
  linarith

/-- Tangent-at-r Gram moment bound; no division by the matrix order is needed. -/
theorem trace_gram_square_lower (A : Matrix ι ι ℤ) (hA : Binary A) (r : ℤ) :
    (4 * r - 1) * (∑ i, rowDegree A i) - 2 * Fintype.card ι * r ^ 2 + 4 * cycleCount A ≤
      Matrix.trace ((Matrix.of (gram A)) * (Matrix.of (gram A))) := by
  rw [trace_gram_square A hA]
  have hrow := degree_squares_lower (rowDegree A) r
  have hcol := degree_squares_lower (columnDegree A) r
  rw [← row_column_degree_sum] at hcol
  linarith

end SparseComponent
