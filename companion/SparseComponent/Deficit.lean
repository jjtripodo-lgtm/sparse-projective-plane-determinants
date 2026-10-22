import SparseComponent.SpectralMoments
import SparseComponent.Constants

namespace SparseComponent
open Finset Matrix Real
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

theorem eigenvalues_log_sum (A : Matrix ι ι ℤ) (hdet : A.det ≠ 0) :
    (∑ i, log (eigenvalues A i)) = 2 * log |(A.det : ℝ)| := by
  rw [← Real.log_prod (fun i _ => (eigenvalues_positive A hdet i).ne')]
  have hp := (realGram_posSemidef A).isHermitian.det_eq_prod_eigenvalues
  simp only [RCLike.ofReal_real_eq_id, id_eq] at hp
  unfold eigenvalues
  rw [← hp, realGram_det, log_pow, log_abs]
  norm_num

/-- The quantitative determinant deficit before the integer component charges. -/
theorem determinant_log_deficit (A : Matrix ι ι ℤ) (hA : Binary A) (hdet : A.det ≠ 0)
    (r : ℕ) (hr : 2 ≤ r) (hc : ∀ k, columnDegree A k ≤ r)
    (hd : ∀ i, rowDegree A i ≤ r) :
    log |(A.det : ℝ)| ≤ (Fintype.card ι : ℝ) * blockLogRate r -
      delta r / 2 * (degreeDeficit A r : ℝ) -
      2 * gamma r * (cycleCount A : ℝ) -
      stabilityCoefficient r * (totalDefect A r : ℝ) := by
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have ht : (0 : ℝ) < r - 1 := by linarith
  have htR : (r : ℝ) - 1 < (r : ℝ) ^ 2 := by nlinarith
  have hrZ : (0 : ℤ) ≤ r := by positivity
  have hmajor : ∀ i, log (eigenvalues A i) +
      (eigenvalues A i - ((r : ℝ) - 1)) ^ 2 * ((r : ℝ) ^ 2 - eigenvalues A i) /
        (3 * ((r : ℝ) ^ 2) ^ 3) ≤
      logA ((r : ℝ) - 1) ((r : ℝ) ^ 2) +
        logB ((r : ℝ) - 1) ((r : ℝ) ^ 2) * eigenvalues A i -
        gamma r * eigenvalues A i ^ 2 := by
    intro i
    apply explicit_log_majorant _ _ ht htR _ (eigenvalues_positive A hdet i)
    simpa using eigenvalues_cap A hA (r : ℤ) hrZ hc hd i
  have hs := sum_le_sum (s := univ) (fun i _ => hmajor i)
  simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← sum_div,
    sum_const, nsmul_eq_mul, card_univ] at hs
  have hcubic := eigenvalues_cubic_sum A (r : ℤ)
  simp only [Int.cast_natCast] at hcubic
  rw [eigenvalues_log_sum A hdet, hcubic, eigenvalues_sum A hA, eigenvalues_square_sum A] at hs
  have hpow : ((r : ℝ) ^ 2) ^ 3 = (r : ℝ) ^ 6 := by ring
  rw [hpow] at hs
  have hm : (4 * (r : ℝ) - 1) * ((∑ i, rowDegree A i : ℤ) : ℝ) -
      2 * Fintype.card ι * (r : ℝ) ^ 2 + 4 * (cycleCount A : ℝ) ≤
      ((Matrix.trace ((Matrix.of (gram A)) * (Matrix.of (gram A))) : ℤ) : ℝ) := by
    exact_mod_cast trace_gram_square_lower A hA (r : ℤ)
  have hgm := mul_le_mul_of_nonneg_left hm (gamma_positive r hrR).le
  have hE : (degreeDeficit A r : ℝ) = (r : ℝ) * Fintype.card ι - ((∑ i, rowDegree A i : ℤ) : ℝ) := by
    rw [degreeDeficit_eq]
    simp [rowDegree]
  have hbase := base_polynomial_value r hrR
  have hcoef := tangent_coefficient (r : ℝ)
  have hexact : (Fintype.card ι : ℝ) * logA ((r : ℝ) - 1) ((r : ℝ) ^ 2) +
      logB ((r : ℝ) - 1) ((r : ℝ) ^ 2) * ((∑ i, rowDegree A i : ℤ) : ℝ) -
      gamma r * ((4 * (r : ℝ) - 1) * ((∑ i, rowDegree A i : ℤ) : ℝ) -
        2 * Fintype.card ι * (r : ℝ) ^ 2 + 4 * (cycleCount A : ℝ)) =
      2 * Fintype.card ι * blockLogRate r - delta r * (degreeDeficit A r : ℝ) -
        4 * gamma r * (cycleCount A : ℝ) := by
    rw [hE, ← hcoef]
    nlinarith [congrArg (fun x : ℝ => (Fintype.card ι : ℝ) * x) hbase]
  have hbound : 2 * log |(A.det : ℝ)| + (totalDefect A r : ℝ) / (3 * (r : ℝ) ^ 6) ≤
      2 * Fintype.card ι * blockLogRate r - delta r * (degreeDeficit A r : ℝ) -
        4 * gamma r * (cycleCount A : ℝ) := by
    rw [← hexact]
    linarith
  have htcoef : (totalDefect A r : ℝ) / (3 * (r : ℝ) ^ 6) =
      2 * stabilityCoefficient r * (totalDefect A r : ℝ) := by
    unfold stabilityCoefficient
    field_simp
    ring
  rw [htcoef] at hbound
  linarith

end SparseComponent
