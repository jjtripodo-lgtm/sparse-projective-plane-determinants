import SparseComponent.Exceptional

namespace SparseComponent
open Finset
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem component_eq_of_mem (A : ι → κ → ℤ) {i j : ι}
    (hj : j ∈ component A i) : component A j = component A i := by
  ext k
  simp only [mem_component]
  have hij := (mem_component A i j).mp hj
  constructor
  · exact fun h => hij.trans h
  · exact fun h => (connected_symm _ (gram_symm A) hij).trans h

theorem component_eq_of_intersect (A : ι → κ → ℤ) {i j k : ι}
    (hi : k ∈ component A i) (hj : k ∈ component A j) :
    component A i = component A j :=
  (component_eq_of_mem A hi).symm.trans (component_eq_of_mem A hj)

noncomputable def components (A : ι → κ → ℤ) : Finset (Finset ι) := by
  classical
  exact univ.image (component A)

@[simp] theorem mem_components (A : ι → κ → ℤ) (C : Finset ι) :
    C ∈ components A ↔ ∃ i, component A i = C := by
  classical
  simp [components]

theorem components_disjoint (A : ι → κ → ℤ) :
    (↑(components A) : Set (Finset ι)).PairwiseDisjoint id := by
  intro C hC D hD hne
  obtain ⟨i, rfl⟩ := (mem_components A C).mp hC
  obtain ⟨j, rfl⟩ := (mem_components A D).mp hD
  apply disjoint_left.mpr
  intro k hki hkj
  exact hne (component_eq_of_intersect A hki hkj)

theorem components_union [DecidableEq ι] (A : ι → κ → ℤ) : (components A).biUnion id = univ := by
  classical
  ext i
  simp only [mem_biUnion, id_eq, mem_univ, iff_true]
  exact ⟨component A i, (mem_components A _).mpr ⟨i, rfl⟩, self_mem_component A i⟩

theorem sum_components (A : ι → κ → ℤ) (f : ι → ℤ) :
    (∑ C ∈ components A, ∑ i ∈ C, f i) = ∑ i, f i := by
  classical
  simpa only [id_eq, components_union] using (sum_biUnion (f := f) (components_disjoint A)).symm

theorem component_gram_closed (A : ι → κ → ℤ) (i : ι) {j k : ι}
    (hj : j ∈ component A i) (hk : k ∉ component A i) : gram A j k = 0 := by
  apply gram_eq_zero_of_not_connected
  intro hjk
  exact hk ((mem_component A i k).mpr (((mem_component A i j).mp hj).trans hjk))

theorem sum_gram_component (A : ι → κ → ℤ) (i : ι) {j : ι}
    (hj : j ∈ component A i) : (∑ k ∈ component A i, gram A j k) = rowSum (gram A) j := by
  classical
  apply sum_subset (subset_univ _)
  intro k hk hkC
  exact component_gram_closed A i hj hkC

end SparseComponent
