import SparseComponent.Deficit

namespace SparseComponent
open Finset Matrix Real
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- Component-count log stability, with every hypothesis expressed on the input matrix. -/
theorem determinant_log_component_stability (A : Matrix ι ι ℤ) (hA : Binary A)
    (hdet : A.det ≠ 0) (r : ℕ) (hr : 2 ≤ r)
    (hc : ∀ k, columnDegree A k ≤ r) (hd : ∀ i, rowDegree A i ≤ r) :
    log |(A.det : ℝ)| ≤ (Fintype.card ι : ℝ) * blockLogRate r -
      stabilityCoefficient r * (residualRows A r : ℝ) := by
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hpos : 0 < stabilityCoefficient r := stabilityCoefficient_positive r (by linarith)
  have hE : (0 : ℝ) ≤ (degreeDeficit A r : ℝ) := by
    exact_mod_cast (show 0 ≤ degreeDeficit A r from
      sum_nonneg (fun i _ => sub_nonneg.mpr (hd i)))
  have hC : (0 : ℝ) ≤ (cycleCount A : ℝ) := by
    exact_mod_cast (show 0 ≤ cycleCount A from
      sum_nonneg (fun i _ => sum_nonneg (fun j _ => cycleWeight_nonneg A hA i j)))
  have hN : (residualRows A r : ℝ) ≤ (totalDefect A r : ℝ) +
      planeOrder r * (cycleCount A : ℝ) + (degreeDeficit A r : ℝ) := by
    have hi := integer_component_extraction A hA (distinctColumns_of_det_ne_zero A hdet)
      (r : ℤ) (by exact_mod_cast hr) hc hd
    unfold planeOrder
    exact_mod_cast hi
  have hcharge := mul_le_mul_of_nonneg_left hN hpos.le
  have hEc := mul_le_mul_of_nonneg_right (delta_charge_constant r hr) hE
  have hCc := mul_le_mul_of_nonneg_right (gamma_charge_constant r hrR) hC
  have hdef := determinant_log_deficit A hA hdet r hr hc hd
  nlinarith

/-- The all-order theorem in exponential form, including singular and empty matrices. -/
theorem determinant_component_stability_exp (A : Matrix ι ι ℤ) (hA : Binary A)
    (r : ℕ) (hr : 2 ≤ r)
    (hc : ∀ k, columnDegree A k ≤ r) (hd : ∀ i, rowDegree A i ≤ r) :
    |(A.det : ℝ)| ≤ exp ((Fintype.card ι : ℝ) * blockLogRate r -
      stabilityCoefficient r * (residualRows A r : ℝ)) := by
  by_cases hdet : A.det = 0
  · simp only [hdet, Int.cast_zero, abs_zero]
    exact (exp_pos _).le
  · apply (log_le_iff_le_exp (abs_pos.mpr (by exact_mod_cast hdet))).mp
    exact determinant_log_component_stability A hA hdet r hr hc hd

noncomputable def designBlockDet (r : ℝ) : ℝ :=
  r * (r - 1) ^ ((planeOrder r - 1) / 2)

theorem designBlockDet_positive (r : ℝ) (hr : 2 ≤ r) : 0 < designBlockDet r := by
  have hr0 : 0 < r := by linarith
  have ht : 0 < r - 1 := by linarith
  unfold designBlockDet
  exact mul_pos hr0 (rpow_pos_of_pos ht _)

theorem designBlockDet_log (r : ℝ) (hr : 2 ≤ r) :
    log (designBlockDet r) / planeOrder r = blockLogRate r := by
  have hr0 : 0 < r := by linarith
  have ht : 0 < r - 1 := by linarith
  unfold designBlockDet blockLogRate
  rw [log_mul hr0.ne' (rpow_pos_of_pos ht _).ne', log_rpow ht]

/-- The stated universal determinant theorem: the projective-plane block bound times an
exponential penalty for the literal rows outside exact plane support components. -/
theorem determinant_component_stability (A : Matrix ι ι ℤ) (hA : Binary A)
    (r : ℕ) (hr : 2 ≤ r)
    (hc : ∀ k, columnDegree A k ≤ r) (hd : ∀ i, rowDegree A i ≤ r) :
    |(A.det : ℝ)| ≤ designBlockDet r ^ ((Fintype.card ι : ℝ) / planeOrder r) *
      exp (-(residualRows A r : ℝ) / (6 * (r : ℝ) ^ 6)) := by
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have he := determinant_component_stability_exp A hA r hr hc hd
  rw [rpow_def_of_pos (designBlockDet_positive r hrR), ← exp_add]
  convert he using 1
  congr 1
  rw [← designBlockDet_log r hrR]
  unfold stabilityCoefficient
  ring

/-- Near extremality bounds the actual residual row count. -/
theorem residualRows_le_log_deficit (A : Matrix ι ι ℤ) (hA : Binary A)
    (hdet : A.det ≠ 0) (r : ℕ) (hr : 2 ≤ r)
    (hc : ∀ k, columnDegree A k ≤ r) (hd : ∀ i, rowDegree A i ≤ r) :
    (residualRows A r : ℝ) ≤ 6 * (r : ℝ) ^ 6 *
      ((Fintype.card ι : ℝ) / planeOrder r * log (designBlockDet r) - log |(A.det : ℝ)|) := by
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hp : (0 : ℝ) < 6 * (r : ℝ) ^ 6 := by positivity
  have h := determinant_log_component_stability A hA hdet r hr hc hd
  rw [← designBlockDet_log r hrR] at h
  unfold stabilityCoefficient at h
  rw [mul_comm (6 * (r : ℝ) ^ 6)]
  apply (div_le_iff₀ hp).mp
  simp only [div_eq_mul_inv] at h ⊢
  nlinarith

end SparseComponent
