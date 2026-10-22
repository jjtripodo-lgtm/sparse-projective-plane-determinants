import SparseComponent.TotalOnes.Normalization

namespace SparseComponent.TotalOnes
open Finset Matrix
open scoped ComplexOrder
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

noncomputable def normalizedEigenvalues (A : Matrix ι ι ℤ) : ι → ℝ :=
  (normalizedGram_posSemidef A).isHermitian.eigenvalues

theorem normalizedEigenvalues_nonneg (A : Matrix ι ι ℤ) (i : ι) :
    0 ≤ normalizedEigenvalues A i :=
  (normalizedGram_posSemidef A).eigenvalues_nonneg i

theorem normalizedEigenvalues_prod (A : Matrix ι ι ℤ) :
    (∏ i, normalizedEigenvalues A i) = (normalizedGram A).det := by
  simpa only [normalizedEigenvalues, RCLike.ofReal_real_eq_id, id_eq] using
    (normalizedGram_posSemidef A).isHermitian.det_eq_prod_eigenvalues.symm

theorem normalizedEigenvalues_sum (A : Matrix ι ι ℤ) :
    (∑ i, normalizedEigenvalues A i) = (normalizedGram A).trace := by
  simpa only [normalizedEigenvalues, RCLike.ofReal_real_eq_id, id_eq] using
    (normalizedGram_posSemidef A).isHermitian.trace_eq_sum_eigenvalues.symm

theorem normalizedEigenvalues_square_sum (A : Matrix ι ι ℤ) :
    (∑ i, normalizedEigenvalues A i ^ 2) =
      (normalizedGram A * normalizedGram A).trace :=
  (spectral_square_trace (normalizedGram A) (normalizedGram_posSemidef A).isHermitian).symm

theorem normalizedEigenvalues_positive (A : Matrix ι ι ℤ) (hdet : A.det ≠ 0)
    (hd : ∀ i, 0 < rowDegree A i) (hc : ∀ j, 0 < columnDegree A j) (i : ι) :
    0 < normalizedEigenvalues A i := by
  have hp : (∏ j, normalizedEigenvalues A j) ≠ 0 := by
    rw [normalizedEigenvalues_prod]
    exact ne_of_gt (normalizedGram_det_pos A hdet hd hc)
  exact lt_of_le_of_ne (normalizedEigenvalues_nonneg A i)
    (Ne.symm ((prod_ne_zero_iff.mp hp) i (mem_univ i)))

theorem normalizedEigenvalues_log_sum (A : Matrix ι ι ℤ) (hdet : A.det ≠ 0)
    (hd : ∀ i, 0 < rowDegree A i) (hc : ∀ j, 0 < columnDegree A j) :
    (∑ i, Real.log (normalizedEigenvalues A i)) = Real.log (normalizedGram A).det := by
  rw [← normalizedEigenvalues_prod, Real.log_prod]
  exact fun i _ => ne_of_gt (normalizedEigenvalues_positive A hdet hd hc i)

theorem normalizedMatrix_nonneg (A : Matrix ι ι ℤ) (hA : Binary A) (i j : ι) :
    0 ≤ normalizedMatrix A i j := by
  exact div_nonneg (by exact_mod_cast binary_nonneg A hA i j)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

theorem normalizedGram_nonneg (A : Matrix ι ι ℤ) (hA : Binary A) (i j : ι) :
    0 ≤ normalizedGram A i j := by
  change 0 ≤ 9 * ∑ k, normalizedMatrix A i k * normalizedMatrix A j k
  exact mul_nonneg (by norm_num) (sum_nonneg fun k _ =>
    mul_nonneg (normalizedMatrix_nonneg A hA i k) (normalizedMatrix_nonneg A hA j k))

theorem normalizedMatrix_mulVec_sqrt_column (A : Matrix ι ι ℤ)
    (hd : ∀ i, 0 < rowDegree A i) (hc : ∀ j, 0 < columnDegree A j) :
    normalizedMatrix A *ᵥ (fun j => Real.sqrt (columnSize A j)) =
      fun i => Real.sqrt (rowSize A i) := by
  ext i
  have hr := ne_of_gt (Real.sqrt_pos.mpr (rowSize_pos A hd i))
  have hterm (j : ι) : normalizedMatrix A i j * Real.sqrt (columnSize A j) =
      (A i j : ℝ) / Real.sqrt (rowSize A i) := by
    have hs := ne_of_gt (Real.sqrt_pos.mpr (columnSize_pos A hc j))
    unfold normalizedMatrix
    field_simp
  change (∑ j, normalizedMatrix A i j * Real.sqrt (columnSize A j)) = _
  simp_rw [hterm]
  rw [← sum_div]
  have hsum : (∑ j, (A i j : ℝ)) = rowSize A i := by simp [rowSize, rowDegree]
  rw [hsum, div_eq_iff hr]
  exact (Real.mul_self_sqrt (rowSize_pos A hd i).le).symm

theorem normalizedMatrix_transpose_mulVec_sqrt_row (A : Matrix ι ι ℤ)
    (hd : ∀ i, 0 < rowDegree A i) (hc : ∀ j, 0 < columnDegree A j) :
    (normalizedMatrix A).transpose *ᵥ (fun i => Real.sqrt (rowSize A i)) =
      fun j => Real.sqrt (columnSize A j) := by
  ext j
  have hs := ne_of_gt (Real.sqrt_pos.mpr (columnSize_pos A hc j))
  have hterm (i : ι) : normalizedMatrix A i j * Real.sqrt (rowSize A i) =
      (A i j : ℝ) / Real.sqrt (columnSize A j) := by
    have hr := ne_of_gt (Real.sqrt_pos.mpr (rowSize_pos A hd i))
    unfold normalizedMatrix
    field_simp
  change (∑ i, normalizedMatrix A i j * Real.sqrt (rowSize A i)) = _
  simp_rw [hterm]
  rw [← sum_div]
  have hsum : (∑ i, (A i j : ℝ)) = columnSize A j := by simp [columnSize, columnDegree]
  rw [hsum, div_eq_iff hs]
  exact (Real.mul_self_sqrt (columnSize_pos A hc j).le).symm

theorem normalizedGram_mulVec_sqrt_row (A : Matrix ι ι ℤ)
    (hd : ∀ i, 0 < rowDegree A i) (hc : ∀ j, 0 < columnDegree A j) :
    normalizedGram A *ᵥ (fun i => Real.sqrt (rowSize A i)) =
      (9 : ℝ) • (fun i => Real.sqrt (rowSize A i)) := by
  rw [normalizedGram, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
    normalizedMatrix_transpose_mulVec_sqrt_row A hd hc,
    normalizedMatrix_mulVec_sqrt_column A hd hc]

/-- Diagonal similarity converts a positive weighted row cap into an ordinary row cap. -/
theorem eigenvalue_le_weighted_row_cap (B : Matrix ι ι ℝ)
    (hn : ∀ i j, 0 ≤ B i j) (s : ι → ℝ) (hs : ∀ i, 0 < s i)
    (R : ℝ) (hc : ∀ i, ∑ j, B i j * s j ≤ R * s i)
    (v : ι → ℝ) (hv : v ≠ 0) (mu : ℝ) (he : B *ᵥ v = mu • v) : mu ≤ R := by
  let C : Matrix ι ι ℝ := fun i j => B i j * s j / s i
  let w : ι → ℝ := fun i => v i / s i
  apply eigenvalue_le_row_cap C
    (fun i j => div_nonneg (mul_nonneg (hn i j) (hs j).le) (hs i).le) R
    (fun i => by
      change (∑ j, B i j * s j / s i) ≤ R
      rw [← sum_div]
      exact (div_le_iff₀ (hs i)).mpr (hc i)) w
  · intro hw
    apply hv
    funext i
    have hi : v i / s i = 0 := congrFun hw i
    exact (div_eq_zero_iff.mp hi).resolve_right (ne_of_gt (hs i))
  · ext i
    change (∑ j, (B i j * s j / s i) * (v j / s j)) = mu * (v i / s i)
    have hterm (j : ι) : (B i j * s j / s i) * (v j / s j) =
        (B i j * v j) / s i := by
      have hi := ne_of_gt (hs i)
      have hj := ne_of_gt (hs j)
      field_simp
    simp_rw [hterm]
    rw [← sum_div]
    have hi : (∑ j, B i j * v j) = mu * v i := congrFun he i
    rw [hi]
    ring

theorem normalizedEigenvalues_cap (A : Matrix ι ι ℤ) (hA : Binary A)
    (hd : ∀ i, 0 < rowDegree A i) (hc : ∀ j, 0 < columnDegree A j) (i : ι) :
    normalizedEigenvalues A i ≤ 9 := by
  let hG := (normalizedGram_posSemidef A).isHermitian
  apply eigenvalue_le_weighted_row_cap (normalizedGram A) (normalizedGram_nonneg A hA)
    (fun j => Real.sqrt (rowSize A j))
    (fun j => Real.sqrt_pos.mpr (rowSize_pos A hd j)) 9
    (fun j => le_of_eq (congrFun (normalizedGram_mulVec_sqrt_row A hd hc) j))
    (hG.eigenvectorBasis i).ofLp
  · intro hw
    have hz : hG.eigenvectorBasis i = 0 := (WithLp.ofLp_eq_zero 2).mp hw
    exact hG.eigenvectorBasis.orthonormal.linearIndependent.ne_zero i hz
  · exact hG.mulVec_eigenvectorBasis i

end SparseComponent.TotalOnes
