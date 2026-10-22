import SparseComponent.Extraction

namespace SparseComponent
open Finset
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Distinct columns are a weak consequence of nonsingularity. -/
def DistinctColumns (A : ι → κ → ℤ) : Prop := Function.Injective (fun k => fun i => A i k)

theorem shifted_zero_gram (A : ι → κ → ℤ) (hA : Binary A)
    (r : ℤ) (i : ι) (hw : ∀ j, shiftedColumn A r i j = 0) :
    rowDegree A i = r - 1 ∧ ∀ j, j ≠ i → gram A j i = 0 := by
  classical
  constructor
  · have hi := hw i
    simpa [shiftedColumn, gram_diagonal A hA, sub_eq_zero] using hi
  · intro j hj
    have h := hw j
    simpa [shiftedColumn, hj] using h

theorem isolated_column_eq (A : ι → κ → ℤ) (hA : Binary A) (i : ι)
    (hg : ∀ j, j ≠ i → gram A j i = 0) (k : κ) (hik : A i k = 1) :
    ∀ j, j ≠ i → A j k = 0 := by
  intro j hji
  rcases hA j k with h | h
  · exact h
  · have hp := gram_pos_of_shared_column A hA j i k h hik
    rw [hg j hji] at hp
    omega

/-- No two columns can meet a row whose other Gram overlaps vanish. -/
theorem isolated_unique_column (A : ι → κ → ℤ) (hA : Binary A)
    (hinj : DistinctColumns A) (i : ι) (hg : ∀ j, j ≠ i → gram A j i = 0)
    (k l : κ) (hk : A i k = 1) (hl : A i l = 1) : k = l := by
  apply hinj
  funext j
  change A j k = A j l
  by_cases hji : j = i
  · subst j; rw [hk, hl]
  · rw [isolated_column_eq A hA i hg k hk j hji,
      isolated_column_eq A hA i hg l hl j hji]

/-- The zero shifted-column exception is precisely an isolated identity row at r=2. -/
theorem zero_shifted_exception (A : ι → κ → ℤ) (hA : Binary A)
    (hinj : DistinctColumns A) (r : ℤ) (hr : 2 ≤ r) (i : ι)
    (hw : ∀ j, shiftedColumn A r i j = 0) :
    r = 2 ∧ rowDegree A i = 1 ∧ ∃ k, A i k = 1 ∧
      (∀ l, l ≠ k → A i l = 0) ∧ (∀ j, j ≠ i → A j k = 0) := by
  classical
  have hg := shifted_zero_gram A hA r i hw
  have hpos : 0 < rowDegree A i := by omega
  have hkex : ∃ k, A i k = 1 := by
    by_contra h
    push Not at h
    have hz : rowDegree A i = 0 := by
      apply sum_eq_zero
      intro k hk
      exact (hA i k).resolve_right (h k)
    omega
  obtain ⟨k, hk⟩ := hkex
  have hzero : ∀ l, l ≠ k → A i l = 0 := by
    intro l hl
    exact (hA i l).resolve_right (fun hl1 => hl (isolated_unique_column A hA hinj i hg.2 l k hl1 hk))
  have hdeg : rowDegree A i = 1 := by
    unfold rowDegree
    rw [sum_eq_single k (fun l _ hl => hzero l hl) (by simp), hk]
  refine ⟨by omega, hdeg, k, hk, hzero, isolated_column_eq A hA i hg.2 k hk⟩

theorem zero_shifted_component_singleton (A : ι → κ → ℤ) (hA : Binary A)
    (r : ℤ) (i : ι) (hw : ∀ j, shiftedColumn A r i j = 0) :
    component A i = {i} := by
  classical
  have hg := (shifted_zero_gram A hA r i hw).2
  ext j
  simp only [mem_component, mem_singleton]
  constructor
  · intro hj
    induction hj with
    | refl => rfl
    | tail h hjk ih =>
      subst_vars
      by_contra hne
      exact hjk (by rw [gram_symm]; exact hg _ hne)
  · intro h; subst j; exact connected_refl _ _

end SparseComponent
