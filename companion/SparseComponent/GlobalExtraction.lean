import SparseComponent.Stability
import Mathlib.Data.Matrix.Block

namespace SparseComponent
open Finset Matrix
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

noncomputable def planeComponents (A : Matrix ι ι ℤ) (r : ℤ) : Finset (Finset ι) := by
  classical
  exact (components A).filter (PlaneRows A r)

noncomputable def supportColumns (A : Matrix ι ι ℤ) (C : Finset ι) : Finset ι := by
  classical
  exact univ.filter (fun k => ∃ i ∈ C, A i k = 1)

@[simp] theorem mem_planeComponents (A : Matrix ι ι ℤ) (r : ℤ) (C : Finset ι) :
    C ∈ planeComponents A r ↔ C ∈ components A ∧ PlaneRows A r C := by
  classical
  simp [planeComponents]

@[simp] theorem mem_supportColumns (A : Matrix ι ι ℤ) (C : Finset ι) (k : ι) :
    k ∈ supportColumns A C ↔ ∃ i ∈ C, A i k = 1 := by
  classical
  simp [supportColumns]

@[simp] theorem supportColumns_component (A : Matrix ι ι ℤ) (i : ι) :
    supportColumns A (component A i) = componentColumns A i := by
  ext k
  simp

noncomputable def goodRows (A : Matrix ι ι ℤ) (r : ℤ) : Finset ι :=
  (planeComponents A r).biUnion id

noncomputable def goodColumns (A : Matrix ι ι ℤ) (r : ℤ) : Finset ι :=
  (planeComponents A r).biUnion (supportColumns A)

noncomputable def badColumns (A : Matrix ι ι ℤ) (r : ℤ) : Finset ι := univ \ goodColumns A r

theorem goodRows_iff_plane (A : Matrix ι ι ℤ) (r : ℤ) (i : ι) :
    i ∈ goodRows A r ↔ PlaneRows A r (component A i) := by
  classical
  simp only [goodRows, mem_biUnion, id_eq]
  constructor
  · rintro ⟨C, hC, hi⟩
    obtain ⟨hCmem, hp⟩ := (mem_planeComponents A r C).mp hC
    obtain ⟨j, rfl⟩ := (mem_components A C).mp hCmem
    rwa [component_eq_of_mem A hi]
  · intro hp
    exact ⟨component A i, (mem_planeComponents A r _).mpr
      ⟨(mem_components A _).mpr ⟨i, rfl⟩, hp⟩, self_mem_component A i⟩

theorem badRows_eq_compl_goodRows (A : Matrix ι ι ℤ) (r : ℤ) :
    badRows A r = univ \ goodRows A r := by
  classical
  ext i
  simp [badRows, goodRows_iff_plane]

theorem supportColumns_disjoint (A : Matrix ι ι ℤ) (hA : Binary A) :
    (↑(components A) : Set (Finset ι)).PairwiseDisjoint (supportColumns A) := by
  classical
  intro C hC D hD hne
  obtain ⟨i, rfl⟩ := (mem_components A C).mp hC
  obtain ⟨j, rfl⟩ := (mem_components A D).mp hD
  apply disjoint_left.mpr
  intro k hkC hkD
  obtain ⟨a, ha, hak⟩ := (mem_supportColumns A _ k).mp hkC
  obtain ⟨b, hb, hbk⟩ := (mem_supportColumns A _ k).mp hkD
  have hab := connected_of_shared_column A hA a b k hak hbk
  have hib : b ∈ component A i := (mem_component A i b).mpr
    (((mem_component A i a).mp ha).trans hab)
  exact hne (component_eq_of_intersect A hib hb)

theorem plane_component_card_match (A : Matrix ι ι ℤ) (hA : Binary A)
    (r : ℤ) (hr : 2 ≤ r) (hc : ∀ k, columnDegree A k ≤ r)
    (hd : ∀ i, rowDegree A i ≤ r) {C : Finset ι} (hC : C ∈ planeComponents A r) :
    C.card = (supportColumns A C).card := by
  obtain ⟨hm, hp⟩ := (mem_planeComponents A r C).mp hC
  obtain ⟨i, rfl⟩ := (mem_components A C).mp hm
  rw [supportColumns_component]
  exact plane_component_balanced A hA r (by omega) hc hd i hp

theorem good_row_column_card_match (A : Matrix ι ι ℤ) (hA : Binary A)
    (r : ℤ) (hr : 2 ≤ r) (hc : ∀ k, columnDegree A k ≤ r)
    (hd : ∀ i, rowDegree A i ≤ r) : (goodRows A r).card = (goodColumns A r).card := by
  classical
  have hs : planeComponents A r ⊆ components A := filter_subset _ _
  have hrows : (↑(planeComponents A r) : Set (Finset ι)).PairwiseDisjoint id :=
    fun C hC D hD hne => components_disjoint A (hs hC) (hs hD) hne
  have hcols : (↑(planeComponents A r) : Set (Finset ι)).PairwiseDisjoint (supportColumns A) :=
    fun C hC D hD hne => supportColumns_disjoint A hA (hs hC) (hs hD) hne
  rw [goodRows, goodColumns, card_biUnion hrows, card_biUnion hcols]
  apply sum_congr rfl
  exact fun C hC => plane_component_card_match A hA r hr hc hd hC

/-- Deleting the actual bad rows deletes exactly as many columns. -/
theorem residual_row_column_card_match (A : Matrix ι ι ℤ) (hA : Binary A)
    (r : ℤ) (hr : 2 ≤ r) (hc : ∀ k, columnDegree A k ≤ r)
    (hd : ∀ i, rowDegree A i ≤ r) : (badRows A r).card = (badColumns A r).card := by
  rw [badRows_eq_compl_goodRows, badColumns, card_sdiff_of_subset (subset_univ _), card_sdiff_of_subset (subset_univ _),
    good_row_column_card_match A hA r hr hc hd]

abbrev BlockLabel (A : Matrix ι ι ℤ) (r : ℤ) := Option (planeComponents A r)

noncomputable def blockRows (A : Matrix ι ι ℤ) (r : ℤ) : BlockLabel A r → Finset ι
  | none => badRows A r
  | some C => C.1

noncomputable def blockColumns (A : Matrix ι ι ℤ) (r : ℤ) : BlockLabel A r → Finset ι
  | none => badColumns A r
  | some C => supportColumns A C.1

theorem blockRows_unique (A : Matrix ι ι ℤ) (r : ℤ) {b c : BlockLabel A r} {i : ι}
    (hi : i ∈ blockRows A r b) (hj : i ∈ blockRows A r c) : b = c := by
  classical
  cases b with
  | none =>
    cases c with
    | none => rfl
    | some C =>
      have hbad : i ∉ goodRows A r := by
        simpa only [blockRows, badRows_eq_compl_goodRows, mem_sdiff, mem_univ, true_and] using hi
      exact False.elim (hbad (mem_biUnion.mpr ⟨C.1, C.2, hj⟩))
  | some C =>
    cases c with
    | none =>
      have hbad : i ∉ goodRows A r := by
        simpa only [blockRows, badRows_eq_compl_goodRows, mem_sdiff, mem_univ, true_and] using hj
      exact False.elim (hbad (mem_biUnion.mpr ⟨C.1, C.2, hi⟩))
    | some D =>
      have hC := (mem_planeComponents A r C.1).mp C.2
      have hD := (mem_planeComponents A r D.1).mp D.2
      have he : C.1 = D.1 := by
        by_contra hne
        exact (disjoint_left.mp (components_disjoint A hC.1 hD.1 hne)) hi hj
      exact congrArg some (Subtype.ext he)

theorem blockColumns_unique (A : Matrix ι ι ℤ) (hA : Binary A) (r : ℤ)
    {b c : BlockLabel A r} {k : ι}
    (hi : k ∈ blockColumns A r b) (hj : k ∈ blockColumns A r c) : b = c := by
  classical
  cases b with
  | none =>
    cases c with
    | none => rfl
    | some C =>
      have hbad : k ∉ goodColumns A r := by
        simpa only [blockColumns, badColumns, mem_sdiff, mem_univ, true_and] using hi
      exact False.elim (hbad (mem_biUnion.mpr ⟨C.1, C.2, hj⟩))
  | some C =>
    cases c with
    | none =>
      have hbad : k ∉ goodColumns A r := by
        simpa only [blockColumns, badColumns, mem_sdiff, mem_univ, true_and] using hj
      exact False.elim (hbad (mem_biUnion.mpr ⟨C.1, C.2, hi⟩))
    | some D =>
      have hC := (mem_planeComponents A r C.1).mp C.2
      have hD := (mem_planeComponents A r D.1).mp D.2
      have he : C.1 = D.1 := by
        by_contra hne
        exact (disjoint_left.mp (supportColumns_disjoint A hA hC.1 hD.1 hne)) hi hj
      exact congrArg some (Subtype.ext he)

theorem blockRows_cover (A : Matrix ι ι ℤ) (r : ℤ) (i : ι) :
    ∃ b : BlockLabel A r, i ∈ blockRows A r b := by
  classical
  by_cases hp : PlaneRows A r (component A i)
  · refine ⟨some ⟨component A i, ?_⟩, self_mem_component A i⟩
    exact (mem_planeComponents A r _).mpr ⟨(mem_components A _).mpr ⟨i, rfl⟩, hp⟩
  · refine ⟨none, ?_⟩
    simpa [blockRows, badRows] using hp

theorem blockColumns_cover (A : Matrix ι ι ℤ) (r : ℤ) (k : ι) :
    ∃ b : BlockLabel A r, k ∈ blockColumns A r b := by
  classical
  by_cases hk : k ∈ goodColumns A r
  · obtain ⟨C, hC, hkC⟩ := mem_biUnion.mp hk
    exact ⟨some ⟨C, hC⟩, hkC⟩
  · refine ⟨none, ?_⟩
    simpa [blockColumns, badColumns] using hk

theorem block_card_match (A : Matrix ι ι ℤ) (hA : Binary A)
    (r : ℤ) (hr : 2 ≤ r) (hc : ∀ k, columnDegree A k ≤ r)
    (hd : ∀ i, rowDegree A i ≤ r) (b : BlockLabel A r) :
    (blockRows A r b).card = (blockColumns A r b).card := by
  cases b with
  | none => exact residual_row_column_card_match A hA r hr hc hd
  | some C => exact plane_component_card_match A hA r hr hc hd C.2

/-- Every matrix entry across distinct blocks is literally zero. -/
theorem cross_block_zero (A : Matrix ι ι ℤ) (hA : Binary A) (r : ℤ)
    {b c : BlockLabel A r} (hne : b ≠ c) {i k : ι}
    (hi : i ∈ blockRows A r b) (hk : k ∈ blockColumns A r c) : A i k = 0 := by
  classical
  rcases hA i k with hzero | hone
  · exact hzero
  exfalso
  cases b with
  | some C =>
    have hcol : k ∈ blockColumns A r (some C) :=
      (mem_supportColumns A C.1 k).mpr ⟨i, hi, hone⟩
    exact hne (blockColumns_unique A hA r hcol hk)
  | none =>
    cases c with
    | none => exact hne rfl
    | some C =>
      obtain ⟨hm, hp⟩ := (mem_planeComponents A r C.1).mp C.2
      obtain ⟨j, hj⟩ := (mem_components A C.1).mp hm
      have hnot : i ∉ component A j := by
        intro him
        have hi' : i ∈ blockRows A r (some C) := by simpa [blockRows, ← hj] using him
        exact hne (blockRows_unique A r hi hi')
      have hk' : k ∈ componentColumns A j := by
        simpa [blockColumns, ← hj] using hk
      have hz := component_no_incoming A hA j i k hnot hk'
      omega

abbrev RowIndex (A : Matrix ι ι ℤ) (r : ℤ) := Σ b : BlockLabel A r, blockRows A r b
abbrev ColumnIndex (A : Matrix ι ι ℤ) (r : ℤ) := Σ b : BlockLabel A r, blockColumns A r b

noncomputable def rowReindex (A : Matrix ι ι ℤ) (r : ℤ) : RowIndex A r ≃ ι :=
  Equiv.ofBijective (fun p => p.2.1) (by
    constructor
    · rintro ⟨b, i, hi⟩ ⟨c, j, hj⟩ hij
      dsimp at hij
      subst j
      have hbc := blockRows_unique A r hi hj
      subst c
      rfl
    · intro i
      obtain ⟨b, hi⟩ := blockRows_cover A r i
      exact ⟨⟨b, i, hi⟩, rfl⟩)

noncomputable def columnReindex (A : Matrix ι ι ℤ) (hA : Binary A) (r : ℤ) : ColumnIndex A r ≃ ι :=
  Equiv.ofBijective (fun p => p.2.1) (by
    constructor
    · rintro ⟨b, i, hi⟩ ⟨c, j, hj⟩ hij
      dsimp at hij
      subst j
      have hbc := blockColumns_unique A hA r hi hj
      subst c
      rfl
    · intro i
      obtain ⟨b, hi⟩ := blockColumns_cover A r i
      exact ⟨⟨b, i, hi⟩, rfl⟩)

/-- Independent exhaustive row and column reindexings expose the literal block diagonal. -/
theorem literal_block_decomposition (A : Matrix ι ι ℤ) (hA : Binary A) (r : ℤ) :
    A.submatrix (rowReindex A r) (columnReindex A hA r) =
      Matrix.blockDiagonal' (fun b : BlockLabel A r =>
        A.submatrix (fun i : blockRows A r b => i.1) (fun k : blockColumns A r b => k.1)) := by
  classical
  ext ⟨b, i⟩ ⟨c, k⟩
  by_cases hbc : b = c
  · subst c
    simp [Matrix.blockDiagonal'_apply_eq, Matrix.submatrix_apply, rowReindex, columnReindex]
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hbc]
    exact cross_block_zero A hA r hbc i.2 k.2

/-- Every retained block is an exact plane, with its literal rows and columns and no entry edits. -/
theorem retained_block_plane (A : Matrix ι ι ℤ) (hA : Binary A)
    (r : ℤ) (hr : 2 ≤ r) (hc : ∀ k, columnDegree A k ≤ r)
    (hd : ∀ i, rowDegree A i ≤ r) (C : planeComponents A r) :
    (C.1.card : ℤ) = r ^ 2 - r + 1 ∧ C.1.card = (supportColumns A C.1).card ∧
    ∀ i ∈ C.1, ∀ j ∈ C.1, (∑ k ∈ supportColumns A C.1, A i k * A j k) =
      (if i = j then r - 1 else 0) + 1 := by
  obtain ⟨hm, hp⟩ := (mem_planeComponents A r C.1).mp C.2
  obtain ⟨a, ha⟩ := (mem_components A C.1).mp hm
  rw [← ha] at hp ⊢
  rw [supportColumns_component]
  have h := literal_plane_component A hA r hr hc hd a hp
  exact ⟨h.1, h.2.1, h.2.2.1⟩

/-- Full literal deletion certificate: N residual rows, exactly N residual columns,
exhaustive independent reindexings, zero cross-block entries, and exact plane blocks. -/
theorem literal_component_extraction (A : Matrix ι ι ℤ) (hA : Binary A)
    (r : ℤ) (hr : 2 ≤ r) (hc : ∀ k, columnDegree A k ≤ r)
    (hd : ∀ i, rowDegree A i ≤ r) :
    (badRows A r).card = (badColumns A r).card ∧
    (∀ b : BlockLabel A r, (blockRows A r b).card = (blockColumns A r b).card) ∧
    A.submatrix (rowReindex A r) (columnReindex A hA r) =
      Matrix.blockDiagonal' (fun b : BlockLabel A r =>
        A.submatrix (fun i : blockRows A r b => i.1) (fun k : blockColumns A r b => k.1)) ∧
    ∀ C : planeComponents A r, (C.1.card : ℤ) = r ^ 2 - r + 1 ∧
      ∀ i ∈ C.1, ∀ j ∈ C.1, (∑ k ∈ supportColumns A C.1, A i k * A j k) =
        (if i = j then r - 1 else 0) + 1 := by
  refine ⟨residual_row_column_card_match A hA r hr hc hd,
    block_card_match A hA r hr hc hd, literal_block_decomposition A hA r, ?_⟩
  intro C
  have h := retained_block_plane A hA r hr hc hd C
  exact ⟨h.1, h.2.2⟩

end SparseComponent
