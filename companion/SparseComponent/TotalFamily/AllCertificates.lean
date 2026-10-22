import SparseComponent.TotalFamily.Equality
import SparseComponent.TotalFamily.EdgeEquality

namespace SparseComponent.TotalFamily
open Finset Matrix Real TotalOnes

/-- Exact isolated-plane equality classification from explicit coupled scalar certificates. -/
theorem equality_iff_all_plane_from_edge_certificate (r : ℕ) (hr : 2 < r)
    (K : ℤ) (hK : 0 ≤ K) (anchor : ℝ → ℝ)
    (hcert : StrictEdgeCertificate r K anchor)
    (hpeel : ∀ k : ℤ, 0 < k → k ≤ K → log (k:ℝ)+slope r*((r:ℝ)-(k:ℝ)) < rate r)
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) (hA : Binary A) :
    |(A.det:ℝ)| = exp (exponent r n (edgeCount A)) ↔
      ∀ i, PlaneRows A r (component A i) := by
  have hrR : (2:ℝ) < r := by exact_mod_cast hr
  constructor
  · intro heq
    obtain ⟨hd,hc⟩ := equality_regular_from_edge_certificate r hrR K hK anchor hcert hpeel n A hA heq
    have hdI (i) : rowDegree A i = r := by
      have hh : (rowDegree A i:ℝ) = r := hd i
      exact_mod_cast hh
    have hcI (j) : columnDegree A j = r := by
      have hh : (columnDegree A j:ℝ) = r := hc j
      exact_mod_cast hh
    have hedge : edgeCount A = (r:ℤ)*(n:ℤ) := by simp [edgeCount, hdI]; ring
    have he : |(A.det:ℝ)| = exp ((n:ℝ)*rate r) := by
      simpa [exponent, hedge] using heq
    rw [exp_rate_eq_design r n hrR.le] at he
    exact (determinant_attains_iff_all_plane A hA r hr.le (fun j => (hcI j).le)
      (fun i => (hdI i).le)).mp (by simpa only [Fintype.card_fin] using he)
  · intro hp
    have hd := all_plane_rowDegree A hA (r:ℤ) hp
    have hc := all_plane_columnDegree_unconditional A hA (r:ℤ) hp
    have he := all_plane_determinant_eq A hA r hr.le (fun j => (hc j).le) (fun i => (hd i).le) hp
    have hedge : edgeCount A = (r:ℤ)*(n:ℤ) := by simp [edgeCount, hd]; ring
    rw [exponent, hedge]
    simp only [Int.cast_mul, Int.cast_natCast, sub_self, mul_zero, add_zero]
    rw [exp_rate_eq_design r n hrR.le]
    simpa only [Fintype.card_fin] using he
end SparseComponent.TotalFamily
