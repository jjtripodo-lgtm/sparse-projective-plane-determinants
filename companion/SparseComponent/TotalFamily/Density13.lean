import SparseComponent.TotalFamily.Density13.Tail

namespace SparseComponent.TotalFamily.Density13
open Finset Matrix Real TotalOnes
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

theorem certificate : EdgeCertificate 13 2 (cubicAnchor 13) := by
  intro d c hd hc
  by_cases hp : d=13 ∧ c=13
  · rcases hp with ⟨rfl,rfl⟩
    norm_num only [Int.cast_ofNat]
    rw [edgeCost_plane 13 (by norm_num) (cubicAnchor 13) (cubicAnchor_plane 13)] <;> norm_num
  · exact (strict_of_nonplane d c hd hc hp).le

theorem strict_certificate : StrictEdgeCertificate 13 2 (cubicAnchor 13) := by
  refine ⟨certificate, ?_⟩
  intro d c hd hc he
  have hp : d=13 ∧ c=13 := by
    by_contra hn
    have h := strict_of_nonplane d c hd hc hn
    rw [he] at h
    linarith
  exact ⟨by exact_mod_cast hp.1, by exact_mod_cast hp.2⟩

theorem peeling_margin_1 : log (1:ℝ)+slope 13*(13-1) < rate 13 := by
  have hr := log_13_1.1
  have ht := log_12_1.1
  have hk := log_2_1.2
  unfold slope rate planeOrder
  norm_num at hr ht hk ⊢
  linarith [gamma_bounds.2]

theorem peeling_margin_2 : log (2:ℝ)+slope 13*(13-2) < rate 13 := by
  have hr := log_13_1.1
  have ht := log_12_1.1
  have hk := log_2_1.2
  unfold slope rate planeOrder
  norm_num at hr ht hk ⊢
  linarith [gamma_bounds.2]

theorem peeling_certificate (k : ℤ) (hk : 0 < k) (hK : k ≤ 2) :
    log (k:ℝ)+slope 13*(13-(k:ℝ)) < rate 13 := by
  interval_cases k
  · simpa using peeling_margin_1
  · simpa using peeling_margin_2

theorem determinant_total_ones (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) (hA : Binary A) :
    |(A.det:ℝ)| ≤ exp (exponent 13 n (edgeCount A)) :=
  determinant_from_certificate 13 (by norm_num) 2 (by norm_num) (cubicAnchor 13) certificate peeling_certificate n A hA

theorem determinant_equality_iff (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) (hA : Binary A) :
    |(A.det:ℝ)| = exp (exponent 13 n (edgeCount A)) ↔ ∀ i, PlaneRows A 13 (component A i) :=
  equality_iff_all_plane_from_edge_certificate 13 (by norm_num) 2 (by norm_num) (cubicAnchor 13) strict_certificate peeling_certificate n A hA

#print axioms determinant_total_ones
#print axioms determinant_equality_iff
end SparseComponent.TotalFamily.Density13
