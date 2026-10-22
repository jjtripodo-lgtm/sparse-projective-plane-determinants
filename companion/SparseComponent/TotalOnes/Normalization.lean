import SparseComponent.TotalOnes.MatrixDefs
import SparseComponent.SpectralMoments
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp

namespace SparseComponent.TotalOnes
open Finset Matrix
open scoped ComplexOrder
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

theorem rowSize_pos (A : Matrix ι ι ℤ) (hd : ∀ i, 0 < rowDegree A i) (i : ι) :
    0 < rowSize A i := by
  unfold rowSize
  exact_mod_cast hd i

theorem columnSize_pos (A : Matrix ι ι ℤ) (hc : ∀ j, 0 < columnDegree A j) (j : ι) :
    0 < columnSize A j := by
  unfold columnSize
  exact_mod_cast hc j

theorem normalizedGram_posSemidef (A : Matrix ι ι ℤ) :
    (normalizedGram A).PosSemidef := by
  unfold normalizedGram
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
  exact (Matrix.posSemidef_self_mul_conjTranspose _).smul (by norm_num : (0 : ℝ) ≤ 9)

theorem normalizedMatrix_eq_diagonal (A : Matrix ι ι ℤ) :
    normalizedMatrix A =
      Matrix.diagonal (fun i => (Real.sqrt (rowSize A i))⁻¹) * realMatrix A *
      Matrix.diagonal (fun j => (Real.sqrt (columnSize A j))⁻¹) := by
  ext i j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, realMatrix, Matrix.of_apply,
    normalizedMatrix, div_eq_mul_inv, _root_.mul_inv_rev]
  ring

theorem normalizedMatrix_det (A : Matrix ι ι ℤ) :
    (normalizedMatrix A).det = (A.det : ℝ) /
      ((∏ i, Real.sqrt (rowSize A i)) * (∏ j, Real.sqrt (columnSize A j))) := by
  rw [normalizedMatrix_eq_diagonal, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_diagonal, Matrix.det_diagonal, realMatrix_det]
  simp only [prod_inv_distrib]
  ring

theorem normalizedGram_det (A : Matrix ι ι ℤ)
    (hd : ∀ i, 0 < rowDegree A i) (hc : ∀ j, 0 < columnDegree A j) :
    (normalizedGram A).det = (9 : ℝ) ^ Fintype.card ι * (A.det : ℝ) ^ 2 /
      ((∏ i, rowSize A i) * (∏ j, columnSize A j)) := by
  have hr : (∏ i, Real.sqrt (rowSize A i)) ^ 2 = ∏ i, rowSize A i := by
    rw [← prod_pow]
    exact prod_congr rfl fun i _ => Real.sq_sqrt (rowSize_pos A hd i).le
  have hs : (∏ j, Real.sqrt (columnSize A j)) ^ 2 = ∏ j, columnSize A j := by
    rw [← prod_pow]
    exact prod_congr rfl fun j _ => Real.sq_sqrt (columnSize_pos A hc j).le
  rw [normalizedGram, Matrix.det_smul, Matrix.det_mul, Matrix.det_transpose,
    ← pow_two, normalizedMatrix_det, div_pow, mul_pow, hr, hs]
  ring

theorem normalizedGram_det_pos (A : Matrix ι ι ℤ) (hdet : A.det ≠ 0)
    (hd : ∀ i, 0 < rowDegree A i) (hc : ∀ j, 0 < columnDegree A j) :
    0 < (normalizedGram A).det := by
  rw [normalizedGram_det A hd hc]
  have ha : (A.det : ℝ) ≠ 0 := by exact_mod_cast hdet
  exact div_pos (mul_pos (pow_pos (by norm_num) _) (sq_pos_of_ne_zero ha))
    (mul_pos (prod_pos fun i _ => rowSize_pos A hd i)
      (prod_pos fun j _ => columnSize_pos A hc j))

theorem normalized_log_det (A : Matrix ι ι ℤ) (hdet : A.det ≠ 0)
    (hd : ∀ i, 0 < rowDegree A i) (hc : ∀ j, 0 < columnDegree A j) :
    2 * Real.log |(A.det : ℝ)| = Real.log (normalizedGram A).det +
      (∑ i, Real.log (rowSize A i / 3)) +
      (∑ j, Real.log (columnSize A j / 3)) := by
  have ha : (A.det : ℝ) ≠ 0 := by exact_mod_cast hdet
  have hr : (∏ i, rowSize A i) ≠ 0 := prod_ne_zero_iff.mpr fun i _ =>
    ne_of_gt (rowSize_pos A hd i)
  have hc' : (∏ j, columnSize A j) ≠ 0 := prod_ne_zero_iff.mpr fun j _ =>
    ne_of_gt (columnSize_pos A hc j)
  have h9 : Real.log 9 = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [normalizedGram_det A hd hc, Real.log_div
    (mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ ha)) (mul_ne_zero hr hc'),
    Real.log_mul (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ ha),
    Real.log_mul hr hc', Real.log_pow, Real.log_pow,
    Real.log_prod (fun i _ => ne_of_gt (rowSize_pos A hd i)),
    Real.log_prod (fun j _ => ne_of_gt (columnSize_pos A hc j)), h9, Real.log_abs]
  simp_rw [Real.log_div (ne_of_gt (rowSize_pos A hd _)) (by norm_num : (3 : ℝ) ≠ 0)]
  simp_rw [Real.log_div (ne_of_gt (columnSize_pos A hc _)) (by norm_num : (3 : ℝ) ≠ 0)]
  simp only [sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul]
  ring

end SparseComponent.TotalOnes
