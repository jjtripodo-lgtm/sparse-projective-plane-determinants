import SparseComponent.TotalFamily.Interface

namespace SparseComponent.TotalFamily.Density3
open Finset Matrix Real TotalOnes

theorem rate_eq_fanoRate : rate 3 = fanoRate := by
  unfold rate planeOrder fanoRate
  rw [log_twentyfour]
  norm_num

theorem slope_eq_edgeSlope : slope 3 = edgeSlope := by
  unfold slope gamma edgeSlope
  norm_num
  rw [← curvature_eq_logGamma]
  ring

theorem determinant_total_ones (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) (hA : Binary A) :
    |(A.det:ℝ)| ≤ exp (exponent 3 n (edgeCount A)) := by
  simpa only [exponent, rate_eq_fanoRate, slope_eq_edgeSlope] using
    TotalOnes.determinant_total_ones n A hA

theorem determinant_equality_iff (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) (hA : Binary A) :
    |(A.det:ℝ)| = exp (exponent 3 n (edgeCount A)) ↔ ∀ i, PlaneRows A 3 (component A i) := by
  rw [exponent, rate_eq_fanoRate, slope_eq_edgeSlope]
  exact (TotalOnes.determinant_total_ones_equality_iff n A hA).trans
    (fanoBlockDecomposition_iff_all_plane A hA)
end SparseComponent.TotalFamily.Density3
