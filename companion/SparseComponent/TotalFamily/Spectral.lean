import SparseComponent.TotalOnes.NormalizedSpectrum
import SparseComponent.TotalOnes.WeightedMoments
import SparseComponent.Parameters

/-! The degree-normalized spectral bridge, uniformly in the real density r > 1.
All matrix quantities are defined from the original binary integer entries. -/
namespace SparseComponent.TotalFamily
open Finset Matrix Real TotalOnes
open scoped ComplexOrder
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

noncomputable def gram (r : ℝ) (A : Matrix ι ι ℤ) : Matrix ι ι ℝ :=
  r^2 • (normalizedMatrix A * (normalizedMatrix A).transpose)

theorem gram_posSemidef (r : ℝ) (A : Matrix ι ι ℤ) : (gram r A).PosSemidef := by
  unfold gram
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
  exact (Matrix.posSemidef_self_mul_conjTranspose _).smul (sq_nonneg r)

noncomputable def eigenvalues (r : ℝ) (A : Matrix ι ι ℤ) : ι → ℝ :=
  (gram_posSemidef r A).isHermitian.eigenvalues

theorem gram_det (r : ℝ) (A : Matrix ι ι ℤ)
    (hd : ∀ i, 0 < rowDegree A i) (hc : ∀ j, 0 < columnDegree A j) :
    (gram r A).det = (r^2)^Fintype.card ι * (A.det : ℝ)^2 /
      ((∏ i, rowSize A i) * (∏ j, columnSize A j)) := by
  have hr : (∏ i, sqrt (rowSize A i))^2 = ∏ i, rowSize A i := by
    rw [← prod_pow]
    exact prod_congr rfl fun i _ => sq_sqrt (rowSize_pos A hd i).le
  have hs : (∏ j, sqrt (columnSize A j))^2 = ∏ j, columnSize A j := by
    rw [← prod_pow]
    exact prod_congr rfl fun j _ => sq_sqrt (columnSize_pos A hc j).le
  rw [gram, Matrix.det_smul, Matrix.det_mul, Matrix.det_transpose,
    ← pow_two, normalizedMatrix_det, div_pow, mul_pow, hr, hs]
  ring

theorem gram_det_pos (r : ℝ) (hr : 0 < r) (A : Matrix ι ι ℤ) (hdet : A.det ≠ 0)
    (hd : ∀ i, 0 < rowDegree A i) (hc : ∀ j, 0 < columnDegree A j) :
    0 < (gram r A).det := by
  rw [gram_det r A hd hc]
  have ha : (A.det : ℝ) ≠ 0 := by exact_mod_cast hdet
  exact div_pos (mul_pos (pow_pos (sq_pos_of_pos hr) _) (sq_pos_of_ne_zero ha))
    (mul_pos (prod_pos fun i _ => rowSize_pos A hd i)
      (prod_pos fun j _ => columnSize_pos A hc j))

theorem eigenvalues_prod (r : ℝ) (A : Matrix ι ι ℤ) :
    (∏ i, eigenvalues r A i) = (gram r A).det := by
  simpa only [eigenvalues, RCLike.ofReal_real_eq_id, id_eq] using
    (gram_posSemidef r A).isHermitian.det_eq_prod_eigenvalues.symm

theorem eigenvalues_sum (r : ℝ) (A : Matrix ι ι ℤ) :
    (∑ i, eigenvalues r A i) = (gram r A).trace := by
  simpa only [eigenvalues, RCLike.ofReal_real_eq_id, id_eq] using
    (gram_posSemidef r A).isHermitian.trace_eq_sum_eigenvalues.symm

theorem eigenvalues_square_sum (r : ℝ) (A : Matrix ι ι ℤ) :
    (∑ i, eigenvalues r A i^2) = (gram r A * gram r A).trace :=
  (spectral_square_trace (gram r A) (gram_posSemidef r A).isHermitian).symm

theorem eigenvalues_positive (r : ℝ) (hr : 0 < r) (A : Matrix ι ι ℤ) (hdet : A.det ≠ 0)
    (hd : ∀ i, 0 < rowDegree A i) (hc : ∀ j, 0 < columnDegree A j) (i : ι) :
    0 < eigenvalues r A i := by
  have hp : (∏ j, eigenvalues r A j) ≠ 0 := by
    rw [eigenvalues_prod]
    exact ne_of_gt (gram_det_pos r hr A hdet hd hc)
  exact lt_of_le_of_ne ((gram_posSemidef r A).eigenvalues_nonneg i)
    (Ne.symm ((prod_ne_zero_iff.mp hp) i (mem_univ i)))

theorem gram_mulVec_sqrt_row (r : ℝ) (A : Matrix ι ι ℤ)
    (hd : ∀ i, 0 < rowDegree A i) (hc : ∀ j, 0 < columnDegree A j) :
    gram r A *ᵥ (fun i => sqrt (rowSize A i)) = r^2 • (fun i => sqrt (rowSize A i)) := by
  rw [gram, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
    normalizedMatrix_transpose_mulVec_sqrt_row A hd hc,
    normalizedMatrix_mulVec_sqrt_column A hd hc]

theorem gram_nonneg (r : ℝ) (A : Matrix ι ι ℤ) (hA : Binary A) (i j : ι) :
    0 ≤ gram r A i j := by
  change 0 ≤ r^2 * ∑ k, normalizedMatrix A i k * normalizedMatrix A j k
  exact mul_nonneg (sq_nonneg r) (sum_nonneg fun k _ =>
    mul_nonneg (normalizedMatrix_nonneg A hA i k) (normalizedMatrix_nonneg A hA j k))

theorem eigenvalues_cap (r : ℝ) (A : Matrix ι ι ℤ) (hA : Binary A)
    (hd : ∀ i, 0 < rowDegree A i) (hc : ∀ j, 0 < columnDegree A j) (i : ι) :
    eigenvalues r A i ≤ r^2 := by
  let hG := (gram_posSemidef r A).isHermitian
  apply eigenvalue_le_weighted_row_cap (gram r A) (gram_nonneg r A hA)
    (fun j => sqrt (rowSize A j))
    (fun j => sqrt_pos.mpr (rowSize_pos A hd j)) (r^2)
    (fun j => le_of_eq (congrFun (gram_mulVec_sqrt_row r A hd hc) j))
    (hG.eigenvectorBasis i).ofLp
  · intro hw
    have hz : hG.eigenvectorBasis i = 0 := (WithLp.ofLp_eq_zero 2).mp hw
    exact hG.eigenvectorBasis.orthonormal.linearIndependent.ne_zero i hz
  · exact hG.mulVec_eigenvectorBasis i

theorem eigenvalues_log_sum (r : ℝ) (hr : 0 < r) (A : Matrix ι ι ℤ) (hdet : A.det ≠ 0)
    (hd : ∀ i, 0 < rowDegree A i) (hc : ∀ j, 0 < columnDegree A j) :
    (∑ i, log (eigenvalues r A i)) = log (gram r A).det := by
  rw [← eigenvalues_prod, log_prod]
  exact fun i _ => ne_of_gt (eigenvalues_positive r hr A hdet hd hc i)

theorem normalized_log_det (r : ℝ) (hr : 0 < r) (A : Matrix ι ι ℤ) (hdet : A.det ≠ 0)
    (hd : ∀ i, 0 < rowDegree A i) (hc : ∀ j, 0 < columnDegree A j) :
    2 * log |(A.det : ℝ)| = log (gram r A).det +
      (∑ i, log (rowSize A i/r)) + (∑ j, log (columnSize A j/r)) := by
  have ha : (A.det : ℝ) ≠ 0 := by exact_mod_cast hdet
  have hrow : (∏ i, rowSize A i) ≠ 0 := prod_ne_zero_iff.mpr fun i _ =>
    ne_of_gt (rowSize_pos A hd i)
  have hcol : (∏ j, columnSize A j) ≠ 0 := prod_ne_zero_iff.mpr fun j _ =>
    ne_of_gt (columnSize_pos A hc j)
  rw [gram_det r A hd hc, log_div
    (mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ hr.ne')) (pow_ne_zero _ ha)) (mul_ne_zero hrow hcol),
    log_mul (pow_ne_zero _ (pow_ne_zero _ hr.ne')) (pow_ne_zero _ ha),
    log_mul hrow hcol, log_pow, log_pow, log_pow,
    log_prod (fun i _ => ne_of_gt (rowSize_pos A hd i)),
    log_prod (fun j _ => ne_of_gt (columnSize_pos A hc j)), log_abs]
  simp_rw [log_div (ne_of_gt (rowSize_pos A hd _)) hr.ne']
  simp_rw [log_div (ne_of_gt (columnSize_pos A hc _)) hr.ne']
  simp only [sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul]
  push_cast
  ring

theorem gram_trace (r : ℝ) (A : Matrix ι ι ℤ) (hA : Binary A)
    (hd : ∀ i, 0 < rowDegree A i) (hc : ∀ j, 0 < columnDegree A j) :
    (gram r A).trace = r^2 * ∑ i, rowMass A i := by
  rw [gram, Matrix.trace_smul]
  change r^2 * (∑ i, ∑ j, normalizedMatrix A i j * normalizedMatrix A i j) = _
  simp_rw [← pow_two, normalizedMatrix_row_sq_sum A hA hd hc]

theorem gram_second_moment_lower (r : ℝ) (A : Matrix ι ι ℤ) (hA : Binary A)
    (hd : ∀ i, 0 < rowDegree A i) (hc : ∀ j, 0 < columnDegree A j) :
    r^4 * ((∑ i, rowMass A i^2) + (∑ j, columnMass A j^2) -
      ((∑ i, rowMass A i/rowSize A i^2) + (∑ j, columnMass A j/columnSize A j^2))/2) ≤
      (gram r A * gram r A).trace := by
  have h := nonnegative_matrix_fourth_moment_lower (normalizedMatrix A) (normalizedMatrix_nonneg A hA)
  simp_rw [normalizedMatrix_row_sq_sum A hA hd hc,
    normalizedMatrix_column_sq_sum A hA hd hc] at h
  have hq := normalizedMatrix_fourth_sum_le A hA hd hc
  have ht : (gram r A * gram r A).trace = r^4 *
      ((normalizedMatrix A * (normalizedMatrix A).transpose) *
        (normalizedMatrix A * (normalizedMatrix A).transpose)).trace := by
    simp only [gram, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.trace_smul, smul_eq_mul]
    ring
  rw [ht]
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

theorem logdet_hermite (r : ℝ) (hr : 2 ≤ r) (A : Matrix ι ι ℤ) (hA : Binary A)
    (hdet : A.det ≠ 0) (hd : ∀ i, 0 < rowDegree A i) (hc : ∀ j, 0 < columnDegree A j) :
    log (gram r A).det ≤ (Fintype.card ι:ℝ)*logA (r-1) (r^2) +
      logB (r-1) (r^2)*(gram r A).trace - gamma r*(gram r A*gram r A).trace := by
  have hrp : 0 < r := by linarith
  have hp (i : ι) : log (eigenvalues r A i) ≤ logA (r-1) (r^2) +
      logB (r-1) (r^2)*eigenvalues r A i - gamma r*eigenvalues r A i^2 := by
    have he := eigenvalues_cap r A hA hd hc i
    have h := explicit_log_majorant (r-1) (r^2) (by linarith) (by nlinarith [sq_nonneg r])
      (eigenvalues r A i) (eigenvalues_positive r hrp A hdet hd hc i) he
    have hn : 0 ≤ (eigenvalues r A i-(r-1))^2*(r^2-eigenvalues r A i)/(3*(r^2)^3) :=
      div_nonneg (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr he)) (by positivity)
    change _ ≤ logA (r-1) (r^2) + logB (r-1) (r^2)*eigenvalues r A i -
      logGamma (r-1) (r^2)*eigenvalues r A i^2
    linarith
  have h := sum_le_sum (s := (univ : Finset ι)) fun i _ => hp i
  simp only [sum_sub_distrib, sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, ← mul_sum] at h
  rw [eigenvalues_log_sum r hrp A hdet hd hc, eigenvalues_sum, eigenvalues_square_sum] at h
  exact h
end SparseComponent.TotalFamily
