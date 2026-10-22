import SparseComponent.TotalOnes.NormalizedSpectrum
import SparseComponent.TotalOnes.WeightedMoments
import SparseComponent.TotalOnes.DegreeSum
import SparseComponent.Parameters

namespace SparseComponent.TotalOnes
open Finset Matrix Real
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

theorem curvature_eq_logGamma : curvature = logGamma 2 9 := by
  unfold curvature logGamma
  rw [Real.log_div (by norm_num) (by norm_num)]
  norm_num

theorem hermiteConstant_eq_logA : hermiteConstant = logA 2 9 := by
  unfold hermiteConstant logA
  rw [← curvature_eq_logGamma]
  norm_num
  ring

theorem hermiteLinear_eq_logB : hermiteLinear = logB 2 9 := by
  unfold hermiteLinear logB
  rw [← curvature_eq_logGamma]
  norm_num
  ring

/-- The actual Hermite polynomial dominates log throughout the normalized spectrum. -/
theorem hermite_log_upper (x : ℝ) (hx : 0 < x) (hcap : x ≤ 9) :
    log x ≤ hermiteConstant + hermiteLinear*x-curvature*x^2 := by
  have h := explicit_log_majorant 2 9 (by norm_num) (by norm_num) x hx hcap
  rw [← curvature_eq_logGamma, ← hermiteConstant_eq_logA, ← hermiteLinear_eq_logB] at h
  have he : 0 ≤ (x-2)^2*(9-x)/(3*9^3) := by
    exact div_nonneg (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hcap)) (by norm_num)
  linarith

theorem normalized_logdet_upper (A : Matrix ι ι ℤ) (hA : Binary A) (hdet : A.det ≠ 0)
    (hd : ∀ i, 0 < rowDegree A i) (hc : ∀ j, 0 < columnDegree A j) :
    log (normalizedGram A).det ≤ (Fintype.card ι:ℝ)*hermiteConstant +
      hermiteLinear*(normalizedGram A).trace -
        curvature*Matrix.trace (normalizedGram A*normalizedGram A) := by
  have h := sum_le_sum (s := (univ : Finset ι)) fun i _ =>
    hermite_log_upper (normalizedEigenvalues A i)
      (normalizedEigenvalues_positive A hdet hd hc i)
      (normalizedEigenvalues_cap A hA hd hc i)
  simp only [sum_sub_distrib, sum_add_distrib, sum_const, card_univ, nsmul_eq_mul,
    ← mul_sum] at h
  rw [normalizedEigenvalues_log_sum A hdet hd hc, normalizedEigenvalues_sum,
    normalizedEigenvalues_square_sum] at h
  exact h

theorem sum_degreeTerm_expansion (d u : ι → ℝ) :
    (∑ i, degreeTerm (d i) (u i)) =
      (9*hermiteLinear/2)*(∑ i, u i) +
      (81*curvature/2)*(∑ i, u i/(d i)^2) -
      81*curvature*(∑ i, (u i)^2) + (∑ i, log (d i/3)) := by
  have he (i : ι) : degreeTerm (d i) (u i) =
      (9*hermiteLinear/2)*u i+(81*curvature/2)*(u i/(d i)^2)-
      81*curvature*(u i)^2+log (d i/3) := by
    unfold degreeTerm
    simp only [div_eq_mul_inv, _root_.mul_inv_rev]
    ring
  simp_rw [he]
  simp only [sum_add_distrib, sum_sub_distrib, mul_sum]

/-- The source separable inequality, entirely from the actual matrix. -/
theorem minimum_degree_separable (A : Matrix ι ι ℤ) (hA : Binary A) (hdet : A.det ≠ 0)
    (hd : ∀ i, 0 < rowDegree A i) (hc : ∀ j, 0 < columnDegree A j) :
    2*log |(A.det:ℝ)| ≤ (Fintype.card ι:ℝ)*hermiteConstant +
      (∑ i, degreeTerm (rowSize A i) (rowMass A i)) +
      (∑ j, degreeTerm (columnSize A j) (columnMass A j)) := by
  have hn := normalized_log_det A hdet hd hc
  have hs := normalized_logdet_upper A hA hdet hd hc
  rw [normalizedGram_trace A hA hd hc] at hs
  have hm := mul_le_mul_of_nonneg_left
    (normalizedGram_second_moment_lower A hA hd hc) curvature_pos.le
  have hz := sum_rowMass_eq_columnMass A
  rw [sum_degreeTerm_expansion, sum_degreeTerm_expansion, ← hz]
  nlinarith

theorem sum_rowSize_eq_edgeCount (A : Matrix ι ι ℤ) :
    (∑ i, rowSize A i) = (edgeCount A:ℝ) := by
  simp [rowSize, edgeCount]

theorem sum_columnSize_eq_edgeCount (A : Matrix ι ι ℤ) :
    (∑ j, columnSize A j) = (edgeCount A:ℝ) := by
  simp only [columnSize, columnDegree, edgeCount, rowDegree, Int.cast_sum]
  exact sum_comm

theorem row_degree_majorant_sum (A : Matrix ι ι ℤ) (hA : Binary A)
    (hd : ∀ i, 2 ≤ rowDegree A i) (hc : ∀ j, 2 ≤ columnDegree A j) :
    (∑ i, degreeTerm (rowSize A i) (rowMass A i)) ≤
      (Fintype.card ι:ℝ)*baseDegreeValue +
        edgeSlope*((edgeCount A:ℝ)-3*(Fintype.card ι:ℝ)) := by
  have hdp (i : ι) : 0 < rowDegree A i := by linarith [hd i]
  have hcp (j : ι) : 0 < columnDegree A j := by linarith [hc j]
  have h := sum_degree_majorant (rowDegree A) (rowMass A) hd
    (rowMass_nonneg A hA hdp hcp) (weighted_row_balance A hdp hcp)
  change (∑ i, degreeTerm (rowSize A i) (rowMass A i)) ≤
    (Fintype.card ι:ℝ)*baseDegreeValue +
      edgeSlope*((∑ i, rowSize A i)-3*(Fintype.card ι:ℝ)) at h
  rwa [sum_rowSize_eq_edgeCount] at h

theorem column_degree_majorant_sum (A : Matrix ι ι ℤ) (hA : Binary A)
    (hd : ∀ i, 2 ≤ rowDegree A i) (hc : ∀ j, 2 ≤ columnDegree A j) :
    (∑ j, degreeTerm (columnSize A j) (columnMass A j)) ≤
      (Fintype.card ι:ℝ)*baseDegreeValue +
        edgeSlope*((edgeCount A:ℝ)-3*(Fintype.card ι:ℝ)) := by
  have hdp (i : ι) : 0 < rowDegree A i := by linarith [hd i]
  have hcp (j : ι) : 0 < columnDegree A j := by linarith [hc j]
  have h := sum_degree_majorant (columnDegree A) (columnMass A) hc
    (columnMass_nonneg A hA hdp hcp) (weighted_column_balance A hdp hcp)
  change (∑ j, degreeTerm (columnSize A j) (columnMass A j)) ≤
    (Fintype.card ι:ℝ)*baseDegreeValue +
      edgeSlope*((∑ j, columnSize A j)-3*(Fintype.card ι:ℝ)) at h
  rwa [sum_columnSize_eq_edgeCount] at h

/-- The strengthened determinant estimate for literal minimum-degree-two matrices. -/
theorem minimum_degree_log_bound (A : Matrix ι ι ℤ) (hA : Binary A) (hdet : A.det ≠ 0)
    (hd : ∀ i, 2 ≤ rowDegree A i) (hc : ∀ j, 2 ≤ columnDegree A j) :
    log |(A.det:ℝ)| ≤ (Fintype.card ι:ℝ)*fanoRate +
      edgeSlope*((edgeCount A:ℝ)-3*(Fintype.card ι:ℝ)) := by
  have hs := minimum_degree_separable A hA hdet (fun i => by linarith [hd i])
    (fun j => by linarith [hc j])
  have hr := row_degree_majorant_sum A hA hd hc
  have hcol := column_degree_majorant_sum A hA hd hc
  have hb := congrArg (fun z : ℝ => (Fintype.card ι:ℝ)*z) base_identity
  nlinarith

theorem minimum_degree_bound (A : Matrix ι ι ℤ) (hA : Binary A) (hdet : A.det ≠ 0)
    (hd : ∀ i, 2 ≤ rowDegree A i) (hc : ∀ j, 2 ≤ columnDegree A j) :
    |(A.det:ℝ)| ≤ exp ((Fintype.card ι:ℝ)*fanoRate +
      edgeSlope*((edgeCount A:ℝ)-3*(Fintype.card ι:ℝ))) := by
  apply (log_le_iff_le_exp (abs_pos.mpr (by exact_mod_cast hdet))).mp
  exact minimum_degree_log_bound A hA hdet hd hc

/-- Tightness of the actual matrix estimate forces every scalar degree point to be tight. -/
theorem minimum_degree_equality_regular (A : Matrix ι ι ℤ) (hA : Binary A) (hdet : A.det ≠ 0)
    (hd : ∀ i, 2 ≤ rowDegree A i) (hc : ∀ j, 2 ≤ columnDegree A j)
    (heq : |(A.det:ℝ)| = exp ((Fintype.card ι:ℝ)*fanoRate +
      edgeSlope*((edgeCount A:ℝ)-3*(Fintype.card ι:ℝ)))) :
    (∀ i, rowDegree A i = 3) ∧ (∀ j, columnDegree A j = 3) := by
  have hdp (i : ι) : 0 < rowDegree A i := by linarith [hd i]
  have hcp (j : ι) : 0 < columnDegree A j := by linarith [hc j]
  have he : log |(A.det:ℝ)| = (Fintype.card ι:ℝ)*fanoRate +
      edgeSlope*((edgeCount A:ℝ)-3*(Fintype.card ι:ℝ)) := by rw [heq, log_exp]
  have hs := minimum_degree_separable A hA hdet hdp hcp
  have hr := row_degree_majorant_sum A hA hd hc
  have hcol := column_degree_majorant_sum A hA hd hc
  have hb := congrArg (fun z : ℝ => (Fintype.card ι:ℝ)*z) base_identity
  have hrEq : (∑ i, degreeTerm (rowSize A i) (rowMass A i)) =
      (Fintype.card ι:ℝ)*baseDegreeValue +
        edgeSlope*((∑ i, rowSize A i)-3*(Fintype.card ι:ℝ)) := by
    rw [sum_rowSize_eq_edgeCount]
    nlinarith
  have hcEq : (∑ j, degreeTerm (columnSize A j) (columnMass A j)) =
      (Fintype.card ι:ℝ)*baseDegreeValue +
        edgeSlope*((∑ j, columnSize A j)-3*(Fintype.card ι:ℝ)) := by
    rw [sum_columnSize_eq_edgeCount]
    nlinarith
  have hR := (sum_degree_majorant_eq_iff (rowDegree A) (rowMass A) hd
    (rowMass_nonneg A hA hdp hcp) (weighted_row_balance A hdp hcp)).mp hrEq
  have hC := (sum_degree_majorant_eq_iff (columnDegree A) (columnMass A) hc
    (columnMass_nonneg A hA hdp hcp) (weighted_column_balance A hdp hcp)).mp hcEq
  exact ⟨fun i => (hR i).1, fun j => (hC j).1⟩

end SparseComponent.TotalOnes
