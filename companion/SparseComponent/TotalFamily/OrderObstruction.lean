import SparseComponent.TotalFamily.FullFamily

namespace SparseComponent.TotalFamily
open Finset Matrix Real TotalOnes

/-- Counting actual row-overlap components gives an exact order factorization. -/
theorem all_plane_order_factorization {ι κ : Type*} [Fintype ι] [Fintype κ]
    [LinearOrder ι] (A : ι → κ → ℤ) (r : ℤ)
    (hp : ∀ i, PlaneRows A r (component A i)) :
    (Fintype.card ι : ℤ) = (r^2-r+1)*(components A).card := by
  classical
  have h := sum_components A (fun _ => (1:ℤ))
  simp only [sum_const,nsmul_eq_mul,mul_one,card_univ] at h
  have hb : ∀ C ∈ components A, (C.card:ℤ) = r^2-r+1 := by
    intro C hC
    obtain ⟨i,rfl⟩ := (mem_components A C).mp hC
    exact (hp i).1
  rw [sum_congr rfl hb] at h
  simp only [sum_const,nsmul_eq_mul] at h
  calc
    (Fintype.card ι:ℤ) = (components A).card*(r^2-r+1) := h.symm
    _ = (r^2-r+1)*(components A).card := mul_comm _ _

/-- Equality forces the original matrix order to be a multiple of the plane order. -/
theorem determinant_family_order_multiple (r : ℕ) (hr0 : 3 ≤ r) (hr1 : r ≤ 14)
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) (hA : Binary A)
    (he : |(A.det:ℝ)| = exp (exponent r n (edgeCount A))) :
    (n:ℤ) = ((r:ℤ)^2-r+1)*(components A).card := by
  have hp := (determinant_total_family_equality_iff r hr0 hr1 n A hA).mp he
  simpa only [Fintype.card_fin] using all_plane_order_factorization A (r:ℤ) hp

/-- A forbidden order is strict even in the unrestricted all-count bound. -/
theorem determinant_family_strict_of_order_not_dvd (r : ℕ) (hr0 : 3 ≤ r) (hr1 : r ≤ 14)
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) (hA : Binary A)
    (hn : ¬ ((r:ℤ)^2-r+1) ∣ (n:ℤ)) :
    |(A.det:ℝ)| < exp (exponent r n (edgeCount A)) := by
  rcases lt_or_eq_of_le (determinant_total_family r hr0 hr1 n A hA) with h | h
  · exact h
  · exact False.elim (hn ⟨(components A).card, determinant_family_order_multiple r hr0 hr1 n A hA h⟩)

/-- The explicit design-base bound is strict whenever its total-budget input has forbidden order. -/
theorem literal_total_family_strict_of_order_not_dvd (r : ℕ) (hr0 : 3 ≤ r) (hr1 : r ≤ 14)
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : ∀ i j, A i j=0 ∨ A i j=1)
    (he : (∑ i, ∑ j, A i j) ≤ (r:ℤ)*(n:ℤ))
    (hn : ¬ ((r:ℤ)^2-r+1) ∣ (n:ℤ)) :
    |(A.det:ℝ)| < ((r:ℝ)*((r:ℝ)-1)^(((r:ℝ)^2-r)/2))^((n:ℝ)/((r:ℝ)^2-r+1)) := by
  have hlt : |(A.det:ℝ)| < exp ((n:ℝ)*rate r) := by
    rcases lt_or_eq_of_le (determinant_total_family_budget r hr0 hr1 n A hA he) with h | h
    · exact h
    · have hp := (determinant_total_family_budget_equality_iff r hr0 hr1 n A hA he).mp h
      have hc := all_plane_order_factorization A (r:ℤ) hp
      exact False.elim (hn ⟨(components A).card, by simpa only [Fintype.card_fin] using hc⟩)
  rw [exp_rate_eq_design r n (by exact_mod_cast (show 2 ≤ r by omega))] at hlt
  simpa [designBlockDet,planeOrder] using hlt

#print axioms all_plane_order_factorization
#print axioms determinant_family_order_multiple
#print axioms determinant_family_strict_of_order_not_dvd
#print axioms literal_total_family_strict_of_order_not_dvd
end SparseComponent.TotalFamily
