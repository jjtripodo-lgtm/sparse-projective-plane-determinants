import SparseComponent.TotalFamily.Density7.Tail

namespace SparseComponent.TotalFamily.Density7
open Finset Matrix Real TotalOnes
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

theorem certificate : EdgeCertificate 7 1 (linearAnchor 7) := by
  intro d c hd hc
  by_cases hp : d=7 ∧ c=7
  · rcases hp with ⟨rfl,rfl⟩
    norm_num only [Int.cast_ofNat]
    rw [edgeCost_plane 7 (by norm_num) (linearAnchor 7) (linearAnchor_plane 7 (by norm_num))] <;> norm_num
  · exact (strict_of_nonplane d c hd hc hp).le

theorem strict_certificate : StrictEdgeCertificate 7 1 (linearAnchor 7) := by
  refine ⟨certificate, ?_⟩
  intro d c hd hc he
  have hp : d=7 ∧ c=7 := by
    by_contra hn
    have h := strict_of_nonplane d c hd hc hn
    rw [he] at h
    linarith
  exact ⟨by exact_mod_cast hp.1, by exact_mod_cast hp.2⟩

theorem peeling_margin_1 : log (1:ℝ)+slope 7*(7-1) < rate 7 := by
  have hr := log_7_1.1
  have ht := log_6_1.1
  have hk := log_2_1.2
  unfold slope rate planeOrder
  norm_num at hr ht hk ⊢
  linarith [gamma_bounds.2]

theorem peeling_certificate (k : ℤ) (hk : 0 < k) (hK : k ≤ 1) :
    log (k:ℝ)+slope 7*(7-(k:ℝ)) < rate 7 := by
  interval_cases k
  · simpa using peeling_margin_1

theorem determinant_total_ones (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) (hA : Binary A) :
    |(A.det:ℝ)| ≤ exp (exponent 7 n (edgeCount A)) :=
  determinant_from_certificate 7 (by norm_num) 1 (by norm_num) (linearAnchor 7) certificate peeling_certificate n A hA

theorem determinant_equality_iff (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) (hA : Binary A) :
    |(A.det:ℝ)| = exp (exponent 7 n (edgeCount A)) ↔ ∀ i, PlaneRows A 7 (component A i) :=
  equality_iff_all_plane_from_edge_certificate 7 (by norm_num) 1 (by norm_num) (linearAnchor 7) strict_certificate peeling_certificate n A hA

#print axioms determinant_total_ones
#print axioms determinant_equality_iff
end SparseComponent.TotalFamily.Density7
