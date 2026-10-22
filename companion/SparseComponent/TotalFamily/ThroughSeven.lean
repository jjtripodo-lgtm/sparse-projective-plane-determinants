import SparseComponent.TotalFamily.Density3
import SparseComponent.TotalFamily.Density7

namespace SparseComponent.TotalFamily
open Finset Matrix Real TotalOnes

/-- Uniform unrestricted estimate for every density 3 through 7, using only binary entries. -/
theorem determinant_total_through_seven (r : ℕ) (hr0 : 3 ≤ r) (hr1 : r ≤ 7)
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) (hA : Binary A) :
    |(A.det:ℝ)| ≤ exp (exponent r n (edgeCount A)) := by
  interval_cases r <;> norm_num only [Nat.cast_ofNat]
  · exact Density3.determinant_total_ones n A hA
  · exact Density4.determinant_total_ones n A hA
  · exact Density5.determinant_total_ones n A hA
  · exact Density6.determinant_total_ones n A hA
  · exact Density7.determinant_total_ones n A hA

/-- Equality consists exactly of actual isolated projective-plane incidence components. -/
theorem determinant_total_through_seven_equality_iff (r : ℕ) (hr0 : 3 ≤ r) (hr1 : r ≤ 7)
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) (hA : Binary A) :
    |(A.det:ℝ)| = exp (exponent r n (edgeCount A)) ↔ ∀ i, PlaneRows A r (component A i) := by
  interval_cases r <;> norm_num only [Nat.cast_ofNat]
  · exact Density3.determinant_equality_iff n A hA
  · exact Density4.determinant_total_ones_equality_iff n A hA
  · exact Density5.determinant_total_ones_equality_iff n A hA
  · exact Density6.determinant_total_ones_equality_iff n A hA
  · exact Density7.determinant_equality_iff n A hA

/-- Total-budget form; no row or column degree cap is assumed. -/
theorem determinant_total_through_seven_budget (r : ℕ) (hr0 : 3 ≤ r) (hr1 : r ≤ 7)
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) (hA : Binary A)
    (he : edgeCount A ≤ (r:ℤ)*(n:ℤ)) :
    |(A.det:ℝ)| ≤ exp ((n:ℝ)*rate r) := by
  apply (determinant_total_through_seven r hr0 hr1 n A hA).trans
  apply exp_le_exp.mpr
  have hrR : (2:ℝ) < r := by exact_mod_cast (show 2 < r by omega)
  have hb : (edgeCount A:ℝ)-(r:ℝ)*(n:ℝ) ≤ 0 := by exact_mod_cast sub_nonpos.mpr he
  have hm := mul_nonpos_of_nonneg_of_nonpos (slope_pos r hrR).le hb
  unfold exponent
  linarith

/-- Exact equality for a total budget, including the empty matrix. -/
theorem determinant_total_through_seven_budget_equality_iff (r : ℕ) (hr0 : 3 ≤ r) (hr1 : r ≤ 7)
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) (hA : Binary A)
    (he : edgeCount A ≤ (r:ℤ)*(n:ℤ)) :
    |(A.det:ℝ)| = exp ((n:ℝ)*rate r) ↔ ∀ i, PlaneRows A r (component A i) := by
  constructor
  · intro heq
    have hup : exp (exponent r n (edgeCount A)) ≤ exp ((n:ℝ)*rate r) := by
      apply exp_le_exp.mpr
      have hrR : (2:ℝ) < r := by exact_mod_cast (show 2 < r by omega)
      have hb : (edgeCount A:ℝ)-(r:ℝ)*(n:ℝ) ≤ 0 := by exact_mod_cast sub_nonpos.mpr he
      have hm := mul_nonpos_of_nonneg_of_nonpos (slope_pos r hrR).le hb
      unfold exponent
      linarith
    rw [← heq] at hup
    exact (determinant_total_through_seven_equality_iff r hr0 hr1 n A hA).mp
      (le_antisymm (determinant_total_through_seven r hr0 hr1 n A hA) hup)
  · intro hp
    have hd := all_plane_rowDegree A hA (r:ℤ) hp
    have hedge : edgeCount A = (r:ℤ)*(n:ℤ) := by simp [edgeCount, hd]; ring
    have h := (determinant_total_through_seven_equality_iff r hr0 hr1 n A hA).mpr hp
    simpa [exponent, hedge] using h

/-- Source-entry endpoint with the explicit projective-plane determinant base. -/
theorem literal_total_through_seven (r : ℕ) (hr0 : 3 ≤ r) (hr1 : r ≤ 7)
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : ∀ i j, A i j = 0 ∨ A i j = 1)
    (he : (∑ i, ∑ j, A i j) ≤ (r:ℤ)*(n:ℤ)) :
    |(A.det:ℝ)| ≤ ((r:ℝ)*((r:ℝ)-1)^(((r:ℝ)^2-r)/2))^((n:ℝ)/((r:ℝ)^2-r+1)) := by
  have h := determinant_total_through_seven_budget r hr0 hr1 n A hA he
  rw [exp_rate_eq_design r n (by exact_mod_cast (show 2 ≤ r by omega))] at h
  simpa [designBlockDet, planeOrder] using h

/-- Literal density-seven total-budget endpoint, with the design determinant base evaluated. -/
theorem literal_density_seven (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : ∀ i j, A i j = 0 ∨ A i j = 1)
    (he : (∑ i, ∑ j, A i j) ≤ 7*(n:ℤ)) :
    |(A.det:ℝ)| ≤ (153558654482644992:ℝ)^((n:ℝ)/43) := by
  have h := literal_total_through_seven 7 (by norm_num) (by norm_num) n A hA he
  norm_num [Real.rpow_natCast] at h ⊢
  exact h

#print axioms literal_density_seven
#print axioms determinant_total_through_seven
#print axioms determinant_total_through_seven_equality_iff
#print axioms determinant_total_through_seven_budget
#print axioms determinant_total_through_seven_budget_equality_iff
#print axioms literal_total_through_seven
end SparseComponent.TotalFamily
