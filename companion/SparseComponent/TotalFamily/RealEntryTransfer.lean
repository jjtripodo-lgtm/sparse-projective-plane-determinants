import SparseComponent.TotalFamily.FullFamily

namespace SparseComponent.TotalFamily
open Finset Matrix Real TotalOnes

/-- Canonical integer representative of a real zero-one matrix. -/
noncomputable def binaryLift {ι : Type*} (A : Matrix ι ι ℝ) : Matrix ι ι ℤ := by
  classical
  exact fun i j => if A i j=0 then 0 else 1

theorem binaryLift_binary {ι : Type*} (A : Matrix ι ι ℝ) : Binary (binaryLift A) := by
  intro i j
  by_cases h : A i j=0
  · left; simp [binaryLift,h]
  · right; simp [binaryLift,h]

theorem binaryLift_cast {ι : Type*} (A : Matrix ι ι ℝ)
    (hA : ∀ i j, A i j=0 ∨ A i j=1) :
    (binaryLift A).map (fun x => (x:ℝ)) = A := by
  ext i j
  rcases hA i j with h | h <;> simp [binaryLift,h]

theorem binaryLift_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : ∀ i j, A i j=0 ∨ A i j=1) :
    ((binaryLift A).det:ℝ) = A.det := by
  rw [Int.cast_det, binaryLift_cast A hA]

theorem binaryLift_edgeCount {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (hA : ∀ i j, A i j=0 ∨ A i j=1) :
    (edgeCount (binaryLift A):ℝ) = ∑ i, ∑ j, A i j := by
  unfold edgeCount rowDegree
  push_cast
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  exact congrArg (fun M : Matrix ι ι ℝ => M i j) (binaryLift_cast A hA)

/-- Literal real-entry all-count endpoint, with no cast or certificate premise supplied by the caller. -/
theorem determinant_real_total_family (r : ℕ) (hr0 : 3 ≤ r) (hr1 : r ≤ 14)
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, A i j=0 ∨ A i j=1) :
    |A.det| ≤ exp ((n:ℝ)*rate r+slope r*((∑ i, ∑ j, A i j)-(r:ℝ)*(n:ℝ))) := by
  have h := determinant_total_family r hr0 hr1 n (binaryLift A) (binaryLift_binary A)
  rw [binaryLift_det A hA] at h
  simpa only [exponent, binaryLift_edgeCount A hA] using h

/-- The explicit design-base total-budget inequality stated directly for real zero-one entries. -/
theorem literal_real_total_family (r : ℕ) (hr0 : 3 ≤ r) (hr1 : r ≤ 14)
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, A i j=0 ∨ A i j=1)
    (he : (∑ i, ∑ j, A i j) ≤ (r:ℝ)*(n:ℝ)) :
    |A.det| ≤ ((r:ℝ)*((r:ℝ)-1)^(((r:ℝ)^2-r)/2))^((n:ℝ)/((r:ℝ)^2-r+1)) := by
  have hg : (edgeCount (binaryLift A):ℝ) ≤ (r:ℝ)*(n:ℝ) := by
    rw [binaryLift_edgeCount A hA]
    exact he
  have hi : edgeCount (binaryLift A) ≤ (r:ℤ)*(n:ℤ) := by exact_mod_cast hg
  have h := literal_total_family r hr0 hr1 n (binaryLift A) (binaryLift_binary A) hi
  rw [binaryLift_det A hA] at h
  exact h

/-- Real-entry equality is the actual plane classification on the entrywise-identical integer representative. -/
theorem determinant_real_total_family_equality_iff (r : ℕ) (hr0 : 3 ≤ r) (hr1 : r ≤ 14)
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, A i j=0 ∨ A i j=1) :
    |A.det| = exp ((n:ℝ)*rate r+slope r*((∑ i, ∑ j, A i j)-(r:ℝ)*(n:ℝ))) ↔
      ∀ i, PlaneRows (binaryLift A) r (component (binaryLift A) i) := by
  have h := determinant_total_family_equality_iff r hr0 hr1 n (binaryLift A) (binaryLift_binary A)
  rw [binaryLift_det A hA] at h
  simpa only [exponent, binaryLift_edgeCount A hA] using h

/-- Real-entry total-budget equality, including the empty matrix. -/
theorem determinant_real_budget_equality_iff (r : ℕ) (hr0 : 3 ≤ r) (hr1 : r ≤ 14)
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, A i j=0 ∨ A i j=1)
    (he : (∑ i, ∑ j, A i j) ≤ (r:ℝ)*(n:ℝ)) :
    |A.det| = exp ((n:ℝ)*rate r) ↔
      ∀ i, PlaneRows (binaryLift A) r (component (binaryLift A) i) := by
  have hg : (edgeCount (binaryLift A):ℝ) ≤ (r:ℝ)*(n:ℝ) := by
    rw [binaryLift_edgeCount A hA]
    exact he
  have hi : edgeCount (binaryLift A) ≤ (r:ℤ)*(n:ℤ) := by exact_mod_cast hg
  have h := determinant_total_family_budget_equality_iff r hr0 hr1 n (binaryLift A) (binaryLift_binary A) hi
  simpa only [binaryLift_det A hA] using h

/-- Literal design-base equality, directly on real entries and their actual total budget. -/
theorem literal_real_total_family_equality_iff (r : ℕ) (hr0 : 3 ≤ r) (hr1 : r ≤ 14)
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, A i j=0 ∨ A i j=1)
    (he : (∑ i, ∑ j, A i j) ≤ (r:ℝ)*(n:ℝ)) :
    |A.det| = ((r:ℝ)*((r:ℝ)-1)^(((r:ℝ)^2-r)/2))^((n:ℝ)/((r:ℝ)^2-r+1)) ↔
      ∀ i, PlaneRows (binaryLift A) r (component (binaryLift A) i) := by
  have h := determinant_real_budget_equality_iff r hr0 hr1 n A hA he
  rw [exp_rate_eq_design r n (by exact_mod_cast (show 2 ≤ r by omega))] at h
  simpa [designBlockDet, planeOrder] using h

#print axioms literal_real_total_family_equality_iff
#print axioms determinant_real_budget_equality_iff
#print axioms determinant_real_total_family
#print axioms literal_real_total_family
#print axioms determinant_real_total_family_equality_iff
end SparseComponent.TotalFamily
