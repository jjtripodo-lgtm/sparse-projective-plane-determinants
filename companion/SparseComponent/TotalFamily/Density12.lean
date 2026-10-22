import SparseComponent.TotalFamily.Density12.Tail

namespace SparseComponent.TotalFamily.Density12
open Finset Matrix Real TotalOnes
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

theorem certificate : EdgeCertificate 12 2 (cubicAnchor 12) := by
  intro d c hd hc
  by_cases hp : d=12 ∧ c=12
  · rcases hp with ⟨rfl,rfl⟩
    norm_num only [Int.cast_ofNat]
    rw [edgeCost_plane 12 (by norm_num) (cubicAnchor 12) (cubicAnchor_plane 12)] <;> norm_num
  · exact (strict_of_nonplane d c hd hc hp).le

theorem strict_certificate : StrictEdgeCertificate 12 2 (cubicAnchor 12) := by
  refine ⟨certificate, ?_⟩
  intro d c hd hc he
  have hp : d=12 ∧ c=12 := by
    by_contra hn
    have h := strict_of_nonplane d c hd hc hn
    rw [he] at h
    linarith
  exact ⟨by exact_mod_cast hp.1, by exact_mod_cast hp.2⟩

theorem peeling_margin_1 : log (1:ℝ)+slope 12*(12-1) < rate 12 := by
  have hr := log_12_1.1
  have ht := log_11_1.1
  have hk := log_2_1.2
  unfold slope rate planeOrder
  norm_num at hr ht hk ⊢
  linarith [gamma_bounds.2]

theorem peeling_margin_2 : log (2:ℝ)+slope 12*(12-2) < rate 12 := by
  have hr := log_12_1.1
  have ht := log_11_1.1
  have hk := log_2_1.2
  unfold slope rate planeOrder
  norm_num at hr ht hk ⊢
  linarith [gamma_bounds.2]

theorem peeling_certificate (k : ℤ) (hk : 0 < k) (hK : k ≤ 2) :
    log (k:ℝ)+slope 12*(12-(k:ℝ)) < rate 12 := by
  interval_cases k
  · simpa using peeling_margin_1
  · simpa using peeling_margin_2

theorem determinant_total_ones (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) (hA : Binary A) :
    |(A.det:ℝ)| ≤ exp (exponent 12 n (edgeCount A)) :=
  determinant_from_certificate 12 (by norm_num) 2 (by norm_num) (cubicAnchor 12) certificate peeling_certificate n A hA

theorem determinant_equality_iff (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) (hA : Binary A) :
    |(A.det:ℝ)| = exp (exponent 12 n (edgeCount A)) ↔ ∀ i, PlaneRows A 12 (component A i) :=
  equality_iff_all_plane_from_edge_certificate 12 (by norm_num) 2 (by norm_num) (cubicAnchor 12) strict_certificate peeling_certificate n A hA

#print axioms determinant_total_ones
#print axioms determinant_equality_iff
end SparseComponent.TotalFamily.Density12
