import SparseComponent.TotalFamily.FullFamily

namespace SparseComponent.TotalFamily
open Finset Matrix Real TotalOnes

/-- The exact exponential loss for every unused unit of total edge budget. -/
theorem determinant_family_unused_budget_loss (r : ℕ) (hr0 : 3 ≤ r) (hr1 : r ≤ 14)
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) (hA : Binary A) :
    |(A.det:ℝ)| ≤ designBlockDet r^((n:ℝ)/planeOrder r) *
      exp (-slope r*((r:ℝ)*(n:ℝ)-(edgeCount A:ℝ))) := by
  have h := determinant_total_family r hr0 hr1 n A hA
  rw [exponent, exp_add, exp_rate_eq_design r n (by exact_mod_cast (show 2 ≤ r by omega))] at h
  convert h using 1 <;> congr 2 <;> ring

/-- A strict total-budget deficit forces strictness in the plane determinant bound. -/
theorem determinant_family_strict_budget (r : ℕ) (hr0 : 3 ≤ r) (hr1 : r ≤ 14)
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) (hA : Binary A)
    (he : edgeCount A < (r:ℤ)*(n:ℤ)) :
    |(A.det:ℝ)| < designBlockDet r^((n:ℝ)/planeOrder r) := by
  rw [← exp_rate_eq_design r n (by exact_mod_cast (show 2 ≤ r by omega))]
  apply lt_of_le_of_lt (determinant_total_family r hr0 hr1 n A hA)
  apply exp_lt_exp.mpr
  have hrR : (2:ℝ) < r := by exact_mod_cast (show 2 < r by omega)
  have hb : (edgeCount A:ℝ)-(r:ℝ)*(n:ℝ) < 0 := by exact_mod_cast sub_neg.mpr he
  have hm := mul_neg_of_pos_of_neg (slope_pos r hrR) hb
  unfold exponent
  linarith

/-- Equality forces every original row and column to have degree r, and uses the entire budget. -/
theorem determinant_family_equality_degrees (r : ℕ) (hr0 : 3 ≤ r) (hr1 : r ≤ 14)
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) (hA : Binary A)
    (he : |(A.det:ℝ)| = exp (exponent r n (edgeCount A))) :
    (∀ i, rowDegree A i = (r:ℤ)) ∧ (∀ j, columnDegree A j = (r:ℤ)) ∧
      edgeCount A = (r:ℤ)*(n:ℤ) := by
  have hp := (determinant_total_family_equality_iff r hr0 hr1 n A hA).mp he
  have hd := all_plane_rowDegree A hA (r:ℤ) hp
  have hc := all_plane_columnDegree_unconditional A hA (r:ℤ) hp
  refine ⟨hd,hc,?_⟩
  simp [edgeCount, hd]
  ring

#print axioms determinant_family_unused_budget_loss
#print axioms determinant_family_strict_budget
#print axioms determinant_family_equality_degrees
end SparseComponent.TotalFamily
