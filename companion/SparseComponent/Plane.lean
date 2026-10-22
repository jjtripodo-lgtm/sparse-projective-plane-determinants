import SparseComponent.Cycles

namespace SparseComponent
open Finset
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [LinearOrder ι]

/-- Exact projective-plane Gram identity on the indicated rows. Applied only to actual components. -/
def PlaneRows (A : ι → κ → ℤ) (r : ℤ) (C : Finset ι) : Prop :=
  (C.card : ℤ) = r ^ 2 - r + 1 ∧
    ∀ i ∈ C, ∀ j ∈ C, gram A i j = if i = j then r else 1

theorem sum_plane_row (C : Finset ι) (r : ℤ) {i : ι} (hi : i ∈ C) :
    (∑ j ∈ C, if i = j then r else (1 : ℤ)) = C.card + r - 1 := by
  have hh : ∀ j, (if i = j then r else (1 : ℤ)) =
      1 + if j = i then r - 1 else 0 := by
    intro j
    by_cases h : j = i
    · subst j; simp
    · have hij : i ≠ j := Ne.symm h
      simp [h, hij]
  simp_rw [hh]
  rw [sum_add_distrib]
  simp [hi]
  ring

/-- C4-free is the essential extra condition turning a zero defect into a plane. -/
theorem zero_defect_cycle_free_plane (A : ι → κ → ℤ) (hA : Binary A)
    (r : ℤ) (hr : 0 < r) (hc : ∀ k, columnDegree A k ≤ r)
    (hd : ∀ i, rowDegree A i ≤ r) (i : ι) (hz : localDefect A r i = 0)
    (hw : ∃ j, shiftedColumn A r i j ≠ 0)
    (hcycle : cycleCountOn A (component A i) = 0) : PlaneRows A r (component A i) := by
  have hcard := zero_defect_component_card A hA r hr hc hd i hz hw
  have hsat := (zero_defect_nontrivial A hA r hr hc hd i hz hw).2.1
  have hdeg := (zero_defect_nontrivial A hA r hr hc hd i hz hw).2.2
  refine ⟨hcard, ?_⟩
  intro j hj k hk
  have hle : ∀ l ∈ component A i, gram A j l ≤ if j = l then r else 1 := by
    intro l hl
    by_cases hjl : j = l
    · subst l
      simp [gram_diagonal A hA, hdeg j hj]
    · rw [if_neg hjl]
      exact cycleCountOn_zero_overlap A hA _ hcycle hj hl hjl
  have hsum : (∑ l ∈ component A i, ((if j = l then r else 1) - gram A j l)) = 0 := by
    rw [sum_sub_distrib, sum_plane_row _ r hj, hcard, sum_gram_component A i hj, hsat j hj]
    ring
  have hzero := (sum_eq_zero_iff_of_nonneg
    (fun l hl => sub_nonneg.mpr (hle l hl))).mp hsum k hk
  omega

theorem zero_defect_nonplane_cycle_positive (A : ι → κ → ℤ) (hA : Binary A)
    (r : ℤ) (hr : 0 < r) (hc : ∀ k, columnDegree A k ≤ r)
    (hd : ∀ i, rowDegree A i ≤ r) (i : ι) (hz : localDefect A r i = 0)
    (hw : ∃ j, shiftedColumn A r i j ≠ 0)
    (hnp : ¬ PlaneRows A r (component A i)) :
    1 ≤ cycleCountOn A (component A i) := by
  have hn := cycleCountOn_nonneg A hA (component A i)
  have hne : cycleCountOn A (component A i) ≠ 0 := by
    intro h
    exact hnp (zero_defect_cycle_free_plane A hA r hr hc hd i hz hw h)
  omega

end SparseComponent
