import SparseComponent.Spectrum

namespace SparseComponent
open Finset Matrix
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

noncomputable def cubicMatrix (B : Matrix ι ι ℝ) (t R : ℝ) : Matrix ι ι ℝ :=
  (B - t • 1) * (R • 1 - B) * (B - t • 1)

theorem spectral_square_trace (B : Matrix ι ι ℝ) (hB : B.IsHermitian) :
    (B * B).trace = ∑ i, hB.eigenvalues i ^ 2 := by
  let e := Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) hB.eigenvectorUnitary
  have he : B = e (Matrix.diagonal hB.eigenvalues) := by
    simpa only [RCLike.ofReal_real_eq_id, Function.id_comp] using hB.spectral_theorem
  calc
    _ = (e (Matrix.diagonal hB.eigenvalues * Matrix.diagonal hB.eigenvalues)).trace := by
      rw [map_mul, ← he]
    _ = (Matrix.diagonal hB.eigenvalues * Matrix.diagonal hB.eigenvalues).trace := Matrix.trace_map e _
    _ = _ := by simp [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, pow_two]

theorem spectral_cubic_trace (B : Matrix ι ι ℝ) (hB : B.IsHermitian) (t R : ℝ) :
    (cubicMatrix B t R).trace = ∑ i, (hB.eigenvalues i - t) ^ 2 * (R - hB.eigenvalues i) := by
  let e := Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) hB.eigenvectorUnitary
  have he : B = e (Matrix.diagonal hB.eigenvalues) := by
    simpa only [RCLike.ofReal_real_eq_id, Function.id_comp] using hB.spectral_theorem
  have hpoly : cubicMatrix B t R = e (cubicMatrix (Matrix.diagonal hB.eigenvalues) t R) := by
    unfold cubicMatrix
    simp only [map_mul, map_sub, map_smul, map_one]
    rw [← he]
  rw [hpoly, Matrix.trace_map]
  simp only [cubicMatrix, Matrix.smul_one_eq_diagonal, Matrix.diagonal_sub,
    Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  apply sum_congr rfl
  intro i hi
  ring

theorem realGram_square_trace (A : Matrix ι ι ℤ) :
    ((realGram A) * (realGram A)).trace =
      ((Matrix.trace ((Matrix.of (gram A)) * (Matrix.of (gram A))) : ℤ) : ℝ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, realGram, Matrix.of_apply,
    Int.cast_sum, Int.cast_mul]

theorem real_cubic_eq_integer (A : Matrix ι ι ℤ) (r : ℤ) :
    cubicMatrix (realGram A) ((r : ℝ) - 1) ((r : ℝ) ^ 2) =
      Matrix.of (fun i j => (defectMatrix A r i j : ℝ)) := by
  ext i j
  simp only [cubicMatrix, defectMatrix, shiftedMatrix, realGram,
    Matrix.smul_one_eq_diagonal, Matrix.mul_apply, Matrix.sub_apply, Matrix.diagonal_apply,
    Matrix.of_apply, Int.cast_sum, Int.cast_mul, Int.cast_sub, Int.cast_pow, Int.cast_one, Int.cast_ite, Int.cast_zero]

theorem eigenvalues_square_sum (A : Matrix ι ι ℤ) :
    (∑ i, eigenvalues A i ^ 2) =
      ((Matrix.trace ((Matrix.of (gram A)) * (Matrix.of (gram A))) : ℤ) : ℝ) := by
  unfold eigenvalues
  rw [← spectral_square_trace (realGram A) (realGram_posSemidef A).isHermitian, realGram_square_trace]

theorem eigenvalues_cubic_sum (A : Matrix ι ι ℤ) (r : ℤ) :
    (∑ i, (eigenvalues A i - ((r : ℝ) - 1)) ^ 2 * ((r : ℝ) ^ 2 - eigenvalues A i)) =
      (totalDefect A r : ℝ) := by
  unfold eigenvalues
  rw [← spectral_cubic_trace (realGram A) (realGram_posSemidef A).isHermitian, real_cubic_eq_integer,
    totalDefect_eq_trace]
  simp [Matrix.trace, Matrix.diag]

end SparseComponent
