import SparseComponent.TotalOnes.TotalOnes

namespace SparseTotalOnesLiteral
open Matrix Real Finset SparseComponent SparseComponent.TotalOnes

/-- No local degree, spectral, scalar certificate or matrix-bound premise. -/
theorem all_edge_counts (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ)
    (binary : ∀ i j, A i j = 0 ∨ A i j = 1) :
    |(A.det:ℝ)| ≤ exp ((n:ℝ)*(log 24/7) +
      (1/12+5*(((7:ℝ)/2-log (9/2))/49)/2)*
      ((((∑ i, ∑ j, A i j):ℤ):ℝ)-3*(n:ℝ))) :=
  determinant_total_ones_literal n A binary

theorem total_three_n (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ)
    (binary : ∀ i j, A i j = 0 ∨ A i j = 1)
    (ones : (∑ i, ∑ j, A i j) ≤ 3*(n:ℤ)) :
    |(A.det:ℝ)| ≤ (24:ℝ)^((n:ℝ)/7) :=
  determinant_total_three_ones n A binary ones

theorem total_three_n_equality (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ)
    (binary : ∀ i j, A i j = 0 ∨ A i j = 1)
    (ones : (∑ i, ∑ j, A i j) ≤ 3*(n:ℤ)) :
    |(A.det:ℝ)| = (24:ℝ)^((n:ℝ)/7) ↔ FanoBlockDecomposition A :=
  determinant_total_three_ones_equality_iff n A binary ones

/-- Equality extracts actual isolated blocks under exhaustive row/column permutations. -/
theorem equality_extracts_original_blocks (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ)
    (binary : ∀ i j, A i j = 0 ∨ A i j = 1)
    (ones : (∑ i, ∑ j, A i j) ≤ 3*(n:ℤ))
    (tight : |(A.det:ℝ)| = (24:ℝ)^((n:ℝ)/7)) :
    badRows A 3 = ∅ ∧ badColumns A 3 = ∅ ∧
    A.submatrix (rowReindex A 3) (columnReindex A binary 3) =
      Matrix.blockDiagonal' (fun b : BlockLabel A 3 =>
        A.submatrix (fun i : blockRows A 3 b => i.1)
          (fun k : blockColumns A 3 b => k.1)) :=
  fanoBlockDecomposition_literal_blocks A binary ((total_three_n_equality n A binary ones).mp tight)

#print axioms all_edge_counts
#print axioms total_three_n
#print axioms total_three_n_equality
#print axioms equality_extracts_original_blocks
#print SparseComponent.TotalOnes.FanoBlockDecomposition
end SparseTotalOnesLiteral
