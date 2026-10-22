import SparseComponent.Charging

namespace SparseComponent
open Finset
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [LinearOrder ι]

theorem plane_shiftedColumn (A : ι → κ → ℤ) (r : ℤ) (i : ι)
    (hp : PlaneRows A r (component A i)) (j : ι) :
    shiftedColumn A r i j = if j ∈ component A i then 1 else 0 := by
  classical
  by_cases hj : j ∈ component A i
  · rw [if_pos hj]
    unfold shiftedColumn
    rw [hp.2 j hj i (self_mem_component A i)]
    by_cases hji : j = i <;> simp [hji]
  · rw [if_neg hj]
    exact shiftedColumn_eq_zero_outside A r i j (by simpa using hj)

theorem plane_gram_rowSum (A : ι → κ → ℤ) (r : ℤ) (i : ι)
    (hp : PlaneRows A r (component A i)) {j : ι} (hj : j ∈ component A i) :
    rowSum (gram A) j = r ^ 2 := by
  rw [← sum_gram_component A i hj]
  rw [sum_congr rfl (hp.2 j hj), sum_plane_row _ r hj, hp.1]
  ring

theorem plane_localDefect_zero (A : ι → κ → ℤ) (r : ℤ) (i : ι)
    (hp : PlaneRows A r (component A i)) : localDefect A r i = 0 := by
  classical
  unfold localDefect energy
  apply sum_eq_zero
  intro j hj
  by_cases hjC : j ∈ component A i
  · simp only [plane_shiftedColumn A r i hp, if_pos hjC, one_mul]
    have hs : (∑ k, gram A j k * if k ∈ component A i then (1 : ℤ) else 0) =
        rowSum (gram A) j := by
      calc
        _ = ∑ k ∈ component A i, gram A j k := by
          simp [mul_ite, sum_ite, component]
        _ = _ := sum_gram_component A i hjC
    rw [hs, plane_gram_rowSum A r i hp hjC]
    ring
  · rw [plane_shiftedColumn A r i hp j, if_neg hjC, zero_mul]

/-- Every plane-labelled actual row component has the matching square support component. -/
theorem plane_component_balanced (A : ι → κ → ℤ) (hA : Binary A)
    (r : ℤ) (hr : 0 < r) (hc : ∀ k, columnDegree A k ≤ r)
    (hd : ∀ i, rowDegree A i ≤ r) (i : ι)
    (hp : PlaneRows A r (component A i)) :
    (component A i).card = (componentColumns A i).card := by
  apply component_balanced A hA r hr hc hd i (plane_localDefect_zero A r i hp)
  refine ⟨i, ?_⟩
  rw [plane_shiftedColumn A r i hp i, if_pos (self_mem_component A i)]
  norm_num

/-- The restricted biadjacency Gram is literally the global Gram, because all other entries vanish. -/
theorem restricted_component_gram (A : ι → κ → ℤ) (hA : Binary A)
    (i : ι) {j l : ι} (hj : j ∈ component A i) :
    (∑ k ∈ componentColumns A i, A j k * A l k) = gram A j l := by
  classical
  apply sum_subset (subset_univ _)
  intro k hk hkC
  rw [component_no_outgoing A hA i j k hj hkC, zero_mul]

/-- Literal support-isolated square plane block, with exact restricted Gram `(r-1)I+J`. -/
theorem literal_plane_component (A : ι → κ → ℤ) (hA : Binary A)
    (r : ℤ) (hr : 2 ≤ r) (hc : ∀ k, columnDegree A k ≤ r)
    (hd : ∀ i, rowDegree A i ≤ r) (i : ι)
    (hp : PlaneRows A r (component A i)) :
    ((component A i).card : ℤ) = r ^ 2 - r + 1 ∧
    (component A i).card = (componentColumns A i).card ∧
    (∀ j ∈ component A i, ∀ l ∈ component A i,
      (∑ k ∈ componentColumns A i, A j k * A l k) =
        (if j = l then r - 1 else 0) + 1) ∧
    (∀ j ∈ component A i, ∀ k ∉ componentColumns A i, A j k = 0) ∧
    (∀ j ∉ component A i, ∀ k ∈ componentColumns A i, A j k = 0) := by
  refine ⟨hp.1, plane_component_balanced A hA r (by omega) hc hd i hp, ?_, ?_, ?_⟩
  · intro j hj l hl
    rw [restricted_component_gram A hA i hj, hp.2 j hj l hl]
    split_ifs <;> ring
  · intro j hj k hk
    exact component_no_outgoing A hA i j k hj hk
  · intro j hj k hk
    exact component_no_incoming A hA i j k hj hk

end SparseComponent
