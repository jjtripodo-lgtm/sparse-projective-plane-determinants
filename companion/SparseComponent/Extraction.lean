import SparseComponent.Gram

namespace SparseComponent
open Finset
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

noncomputable def shiftedColumn (A : ι → κ → ℤ) (r : ℤ) (i j : ι) : ℤ := by
  classical
  exact gram A j i - if j = i then r - 1 else 0

noncomputable def localDefect (A : ι → κ → ℤ) (r : ℤ) (i : ι) : ℤ :=
  energy (gram A) (r ^ 2) (shiftedColumn A r i)

theorem localDefect_nonneg (A : ι → κ → ℤ) (hA : Binary A)
    (r : ℤ) (hr : 0 ≤ r) (hc : ∀ k, columnDegree A k ≤ r)
    (hd : ∀ i, rowDegree A i ≤ r) (i : ι) : 0 ≤ localDefect A r i :=
  energy_nonneg _ (gram_symm A) (gram_nonneg A hA) _ (gram_rowSum_cap A hA r hr hc hd) _

theorem shiftedColumn_eq_zero_outside (A : ι → κ → ℤ) (r : ℤ) (i j : ι)
    (h : ¬ Connected (gram A) i j) : shiftedColumn A r i j = 0 := by
  have hji : j ≠ i := by intro hj; subst j; exact h (connected_refl _ _)
  unfold shiftedColumn
  rw [if_neg hji, sub_zero, gram_symm]
  exact gram_eq_zero_of_not_connected A h

theorem zero_defect_constant (A : ι → κ → ℤ) (hA : Binary A)
    (r : ℤ) (hr : 0 ≤ r) (hc : ∀ k, columnDegree A k ≤ r)
    (hd : ∀ i, rowDegree A i ≤ r) (i : ι) (hz : localDefect A r i = 0)
    {j : ι} (hj : Connected (gram A) i j) :
    shiftedColumn A r i i = shiftedColumn A r i j :=
  energy_zero_constant_on_component _ (gram_symm A) (gram_nonneg A hA) _
    (gram_rowSum_cap A hA r hr hc hd) _ hz hj

/-- A nonzero shifted column of zero defect extracts a saturated regular row component. -/
theorem zero_defect_nontrivial (A : ι → κ → ℤ) (hA : Binary A)
    (r : ℤ) (hr : 0 < r) (hc : ∀ k, columnDegree A k ≤ r)
    (hd : ∀ i, rowDegree A i ≤ r) (i : ι) (hz : localDefect A r i = 0)
    (hw : ∃ j, shiftedColumn A r i j ≠ 0) :
    (∀ j ∈ component A i, shiftedColumn A r i j = 1) ∧
    (∀ j ∈ component A i, rowSum (gram A) j = r ^ 2) ∧
    (∀ j ∈ component A i, rowDegree A j = r) := by
  obtain ⟨j, hj⟩ := hw
  have hcon : Connected (gram A) i j := by
    by_contra h
    exact hj (shiftedColumn_eq_zero_outside A r i j h)
  have heq := zero_defect_constant A hA r hr.le hc hd i hz hcon
  have hwi : shiftedColumn A r i i ≠ 0 := by rwa [heq]
  have rig := (energy_eq_zero_rigidity _ (gram_symm A) (gram_nonneg A hA) _
    (gram_rowSum_cap A hA r hr.le hc hd) _ hz).1
  have hs : rowSum (gram A) i = r ^ 2 := rig i hwi
  have hdi := rowDegree_of_saturated_gram A hA r hr hc hd i hs
  have hi1 : shiftedColumn A r i i = 1 := by
    simp [shiftedColumn, gram_diagonal A hA, hdi]
  have hall : ∀ j ∈ component A i, shiftedColumn A r i j = 1 := by
    intro j hj
    rw [← zero_defect_constant A hA r hr.le hc hd i hz ((mem_component A i j).mp hj), hi1]
  have hsat : ∀ j ∈ component A i, rowSum (gram A) j = r ^ 2 := by
    intro j hj
    apply rig j
    rw [hall j hj]
    norm_num
  exact ⟨hall, hsat, fun j hj => rowDegree_of_saturated_gram A hA r hr hc hd j (hsat j hj)⟩

/-- A zero-defect component with nonzero shifted column has exactly `r²-r+1` rows. -/
theorem zero_defect_component_card (A : ι → κ → ℤ) (hA : Binary A)
    (r : ℤ) (hr : 0 < r) (hc : ∀ k, columnDegree A k ≤ r)
    (hd : ∀ i, rowDegree A i ≤ r) (i : ι) (hz : localDefect A r i = 0)
    (hw : ∃ j, shiftedColumn A r i j ≠ 0) :
    (component A i).card = r ^ 2 - r + 1 := by
  classical
  have h := zero_defect_nontrivial A hA r hr hc hd i hz hw
  have hrow : (∑ j ∈ component A i, gram A i j) = rowSum (gram A) i := by
    apply sum_subset (subset_univ _)
    intro j hj hjC
    exact gram_eq_zero_of_not_connected A (by simpa using hjC)
  have hg : ∀ j ∈ component A i, gram A i j =
      1 + if j = i then r - 1 else 0 := by
    intro j hj
    have he := h.1 j hj
    unfold shiftedColumn at he
    rw [gram_symm] at he
    omega
  have hs : (∑ j ∈ component A i, gram A i j) = (component A i).card + (r - 1) := by
    rw [sum_congr rfl hg, sum_add_distrib]
    simp [connected_refl]
  rw [hrow, h.2.1 i (self_mem_component A i)] at hs
  omega

noncomputable def componentColumns (A : ι → κ → ℤ) (i : ι) : Finset κ :=
  @Finset.filter κ (fun k => ∃ j ∈ component A i, A j k = 1) (Classical.decPred _) univ

@[simp] theorem mem_componentColumns (A : ι → κ → ℤ) (i : ι) (k : κ) :
    k ∈ componentColumns A i ↔ ∃ j ∈ component A i, A j k = 1 := by
  simp [componentColumns]

theorem component_column_regular (A : ι → κ → ℤ) (hA : Binary A)
    (r : ℤ) (hr : 0 < r) (hc : ∀ k, columnDegree A k ≤ r)
    (hd : ∀ i, rowDegree A i ≤ r) (i : ι) (hz : localDefect A r i = 0)
    (hw : ∃ j, shiftedColumn A r i j ≠ 0) :
    ∀ k ∈ componentColumns A i, columnDegree A k = r := by
  intro k hk
  obtain ⟨j, hj, hjk⟩ := (mem_componentColumns A i k).mp hk
  exact incident_columnDegree_of_saturated_gram A hA r hr hc hd j
    ((zero_defect_nontrivial A hA r hr hc hd i hz hw).2.1 j hj) k hjk

/-- No support edge enters the extracted component from an outside row. -/
theorem component_no_incoming (A : ι → κ → ℤ) (hA : Binary A)
    (i j : ι) (k : κ) (hj : j ∉ component A i) (hk : k ∈ componentColumns A i) :
    A j k = 0 := by
  obtain ⟨a, ha, hak⟩ := (mem_componentColumns A i k).mp hk
  rcases hA j k with h | h
  · exact h
  · exact False.elim (hj ((mem_component A i j).mpr
      (((mem_component A i a).mp ha).trans (connected_of_shared_column A hA a j k hak h))))

/-- No support edge leaves the extracted component. -/
theorem component_no_outgoing (A : ι → κ → ℤ) (hA : Binary A)
    (i j : ι) (k : κ) (hj : j ∈ component A i) (hk : k ∉ componentColumns A i) :
    A j k = 0 := by
  rcases hA j k with h | h
  · exact h
  · exact False.elim (hk ((mem_componentColumns A i k).mpr ⟨j, hj, h⟩))

/-- Double-counting edges makes a saturated positive-degree component square. -/
theorem component_balanced (A : ι → κ → ℤ) (hA : Binary A)
    (r : ℤ) (hr : 0 < r) (hc : ∀ k, columnDegree A k ≤ r)
    (hd : ∀ i, rowDegree A i ≤ r) (i : ι) (hz : localDefect A r i = 0)
    (hw : ∃ j, shiftedColumn A r i j ≠ 0) :
    (component A i).card = (componentColumns A i).card := by
  classical
  have hrow : (∑ j ∈ component A i, ∑ k ∈ componentColumns A i, A j k) =
      (component A i).card * r := by
    calc
      _ = ∑ j ∈ component A i, rowDegree A j := by
        apply sum_congr rfl
        intro j hj
        apply sum_subset (subset_univ _)
        intro k hk hkC
        exact component_no_outgoing A hA i j k hj hkC
      _ = _ := by
        rw [sum_congr rfl (zero_defect_nontrivial A hA r hr hc hd i hz hw).2.2]
        simp
  have hcol : (∑ k ∈ componentColumns A i, ∑ j ∈ component A i, A j k) =
      (componentColumns A i).card * r := by
    calc
      _ = ∑ k ∈ componentColumns A i, columnDegree A k := by
        apply sum_congr rfl
        intro k hk
        apply sum_subset (subset_univ _)
        intro j hj hjC
        exact component_no_incoming A hA i j k hjC hk
      _ = _ := by
        rw [sum_congr rfl (component_column_regular A hA r hr hc hd i hz hw)]
        simp
  rw [sum_comm] at hrow
  rw [hcol] at hrow
  have hcard : ((component A i).card : ℤ) = (componentColumns A i).card := by nlinarith
  exact_mod_cast hcard

end SparseComponent
