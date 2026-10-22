import SparseComponent.TotalOnes.TotalOnes
import SparseComponent.TotalFamily.ConcreteEquality
import SparseComponent.TotalFamily.AllCertificates
import SparseComponent.TotalFamily.Density4
import SparseComponent.TotalFamily.Density5
import SparseComponent.TotalFamily.Density6
import SparseComponent.TotalFamily.Equality
import SparseComponent.TotalFamily.Anchors
import SparseComponent.TotalFamily.LinearTools
import SparseComponent.TotalFamily.EdgeEquality

namespace SparseComponent.TotalFamily
open Finset Matrix Real TotalOnes

/-- Original-entry, total-budget density four endpoint. -/
theorem literal_density_four (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : ∀ i j, A i j = 0 ∨ A i j = 1) (he : (∑ i, ∑ j, A i j) ≤ 4*(n:ℤ)) :
    |(A.det:ℝ)| ≤ (2916:ℝ)^((n:ℝ)/13) := by
  have h := Density4.determinant_total_4_ones n A hA he
  rw [exp_rate_eq_design 4 n (by norm_num)] at h
  norm_num [designBlockDet, planeOrder, Real.rpow_natCast] at h ⊢
  exact h

/-- Original-entry, total-budget density five endpoint. -/
theorem literal_density_five (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : ∀ i j, A i j = 0 ∨ A i j = 1) (he : (∑ i, ∑ j, A i j) ≤ 5*(n:ℤ)) :
    |(A.det:ℝ)| ≤ (5242880:ℝ)^((n:ℝ)/21) := by
  have h := Density5.determinant_total_5_ones n A hA he
  rw [exp_rate_eq_design 5 n (by norm_num)] at h
  norm_num [designBlockDet, planeOrder, Real.rpow_natCast] at h ⊢
  exact h

/-- Original-entry, total-budget density six endpoint. -/
theorem literal_density_six (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : ∀ i j, A i j = 0 ∨ A i j = 1) (he : (∑ i, ∑ j, A i j) ≤ 6*(n:ℤ)) :
    |(A.det:ℝ)| ≤ (183105468750:ℝ)^((n:ℝ)/31) := by
  have h := Density6.determinant_total_6_ones n A hA he
  rw [exp_rate_eq_design 6 n (by norm_num)] at h
  norm_num [designBlockDet, planeOrder, Real.rpow_natCast] at h ⊢
  exact h

#print axioms literal_density_four
#print axioms literal_density_five
#print axioms literal_density_six
#print axioms Density4.determinant_total_budget_equality_iff
#print axioms Density5.determinant_total_budget_equality_iff
#print axioms Density6.determinant_total_budget_equality_iff
#print axioms equality_iff_all_plane_from_edge_certificate
#print axioms determinant_from_certificate
#print axioms equality_regular_from_edge_certificate
end SparseComponent.TotalFamily
