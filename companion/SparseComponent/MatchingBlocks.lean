import SparseComponent.LiteralSupport
import Mathlib.LinearAlgebra.Matrix.Block

namespace SparseComponent
open Finset Matrix
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- A nonzero Leibniz term supplies a literal support perfect matching. -/
theorem exists_support_matching (A : Matrix ι ι ℤ) (hA : Binary A) (hdet : A.det ≠ 0) :
    ∃ σ : Equiv.Perm ι, ∀ i, A i (σ i) = 1 := by
  classical
  have hs : (∑ σ : Equiv.Perm ι, (Equiv.Perm.sign σ : ℤ) * ∏ i, A (σ i) i) ≠ 0 := by
    simpa only [Matrix.det_apply', Int.cast_id] using hdet
  obtain ⟨σ, _, hσ⟩ := exists_ne_zero_of_sum_ne_zero hs
  have hp : (∏ i, A (σ i) i) ≠ 0 := (mul_ne_zero_iff.mp hσ).2
  refine ⟨σ.symm, fun i => ?_⟩
  have hn := (prod_ne_zero_iff.mp hp) (σ.symm i) (mem_univ _)
  simpa using (hA (σ (σ.symm i)) (σ.symm i)).resolve_left hn

noncomputable def matchedBlock (A : Matrix ι ι ℤ) (σ : Equiv.Perm ι) (C : Finset ι) :
    Matrix C C ℤ := Matrix.of (fun i j => A i (σ j))

theorem matching_cross_zero (A : Matrix ι ι ℤ) (hA : Binary A)
    (σ : Equiv.Perm ι) (hσ : ∀ i, A i (σ i) = 1) {i j : ι}
    (hne : component A i ≠ component A j) : A i (σ j) = 0 := by
  rcases hA i (σ j) with h | h
  · exact h
  · exfalso
    apply hne
    have hij := connected_of_shared_column A hA i j (σ j) h (hσ j)
    exact (component_eq_of_mem A ((mem_component A i j).mpr hij)).symm

theorem component_eq_iff_mem (A : Matrix ι ι ℤ) {C : Finset ι}
    (hC : C ∈ components A) (i : ι) : component A i = C ↔ i ∈ C := by
  obtain ⟨j, rfl⟩ := (mem_components A C).mp hC
  exact ⟨fun h => h ▸ self_mem_component A i, fun h => component_eq_of_mem A h⟩

/-- Actual support components factor the determinant; their balance follows from the matching. -/
theorem determinant_matching_blocks (A : Matrix ι ι ℤ) (hA : Binary A)
    (σ : Equiv.Perm ι) (hσ : ∀ i, A i (σ i) = 1) :
    |A.det| = ∏ C ∈ components A, |(matchedBlock A σ C).det| := by
  classical
  let e := Fintype.equivFin (Finset ι)
  let M := A.submatrix id σ
  let b := fun i => e (component A i)
  have hM : M.BlockTriangular b := by
    intro i j hij
    apply matching_cross_zero A hA σ hσ
    intro he
    exact (ne_of_gt hij) (congrArg e he)
  have hprod := hM.det
  have himage : univ.image b = (components A).image e := by
    simp [b, components, image_image, Function.comp_def]
  rw [himage, prod_image (fun _ _ _ _ he => e.injective he)] at hprod
  have heq : ∀ C ∈ components A, (M.toSquareBlock b (e C)).det = (matchedBlock A σ C).det := by
    intro C hC
    have hh := Matrix.equiv_block_det M (p := fun i => b i = e C) (q := fun i => i ∈ C) (fun i => by
      change i ∈ C ↔ e (component A i) = e C
      rw [e.injective.eq_iff]
      exact (component_eq_iff_mem A hC i).symm)
    convert! hh using 1
    have hfi : (Finset.Subtype.fintype C) = (Subtype.fintype fun i => i ∈ C) := Subsingleton.elim _ _
    rw [hfi]
    rfl
  rw [show (∏ C ∈ components A, (M.toSquareBlock b (e C)).det) =
      ∏ C ∈ components A, (matchedBlock A σ C).det from prod_congr rfl heq] at hprod
  have habs : |M.det| = |A.det| := Matrix.abs_det_submatrix_equiv_equiv (Equiv.refl ι) σ A
  rw [← habs, hprod, Finset.abs_prod]

theorem matchedBlock_binary (A : Matrix ι ι ℤ) (hA : Binary A)
    (σ : Equiv.Perm ι) (C : Finset ι) : Binary (matchedBlock A σ C) :=
  fun i j => hA i (σ j)

theorem matchedBlock_rowDegree (A : Matrix ι ι ℤ) (hA : Binary A)
    (σ : Equiv.Perm ι) (hσ : ∀ i, A i (σ i) = 1)
    {C : Finset ι} (hC : C ∈ components A) (i : C) :
    rowDegree (matchedBlock A σ C) i = rowDegree A i := by
  classical
  change (∑ j : C, A i (σ j)) = ∑ j, A i j
  rw [sum_coe_sort C (fun j => A i (σ j))]
  calc
    (∑ j ∈ C, A i (σ j)) = ∑ j, A i (σ j) := by
      apply sum_subset (subset_univ _)
      intro j _ hj
      apply matching_cross_zero A hA σ hσ
      intro he
      have hic := (component_eq_iff_mem A hC i).mpr i.2
      exact hj ((component_eq_iff_mem A hC j).mp (he.symm.trans hic))
    _ = _ := Equiv.sum_comp σ (fun j => A i j)

theorem matchedBlock_columnDegree (A : Matrix ι ι ℤ) (hA : Binary A)
    (σ : Equiv.Perm ι) (hσ : ∀ i, A i (σ i) = 1)
    {C : Finset ι} (hC : C ∈ components A) (j : C) :
    columnDegree (matchedBlock A σ C) j = columnDegree A (σ j) := by
  classical
  change (∑ i : C, A i (σ j)) = ∑ i, A i (σ j)
  rw [sum_coe_sort C (fun i => A i (σ j))]
  apply sum_subset (subset_univ _)
  intro i _ hi
  apply matching_cross_zero A hA σ hσ
  intro he
  exact hi ((component_eq_iff_mem A hC i).mp (he.trans ((component_eq_iff_mem A hC j).mpr j.2)))

theorem matchedBlock_gram (A : Matrix ι ι ℤ) (hA : Binary A)
    (σ : Equiv.Perm ι) (hσ : ∀ i, A i (σ i) = 1)
    {C : Finset ι} (hC : C ∈ components A) (i j : C) :
    gram (matchedBlock A σ C) i j = gram A i j := by
  classical
  change (∑ k : C, A i (σ k) * A j (σ k)) = ∑ k, A i k * A j k
  rw [sum_coe_sort C (fun k => A i (σ k) * A j (σ k))]
  calc
    (∑ k ∈ C, A i (σ k) * A j (σ k)) = ∑ k, A i (σ k) * A j (σ k) := by
      apply sum_subset (subset_univ _)
      intro k _ hk
      have hz : A i (σ k) = 0 := by
        apply matching_cross_zero A hA σ hσ
        intro he
        exact hk ((component_eq_iff_mem A hC k).mp (he.symm.trans ((component_eq_iff_mem A hC i).mpr i.2)))
      rw [hz, zero_mul]
    _ = _ := Equiv.sum_comp σ (fun k => A i k * A j k)

theorem matchedBlock_shiftedColumn (A : Matrix ι ι ℤ) (hA : Binary A)
    (σ : Equiv.Perm ι) (hσ : ∀ i, A i (σ i) = 1)
    {C : Finset ι} (hC : C ∈ components A) (r : ℤ) (i j : C) :
    shiftedColumn (matchedBlock A σ C) r i j = shiftedColumn A r i j := by
  simp only [shiftedColumn, matchedBlock_gram A hA σ hσ hC, Subtype.mk.injEq]
  have he : (j = i) ↔ (j.1 = i.1) := Subtype.ext_iff
  simp only [he]
  congr 1
  split_ifs <;> rfl

theorem matchedBlock_localDefect (A : Matrix ι ι ℤ) (hA : Binary A)
    (σ : Equiv.Perm ι) (hσ : ∀ i, A i (σ i) = 1)
    {C : Finset ι} (hC : C ∈ components A) (r : ℤ) (i : C) :
    localDefect (matchedBlock A σ C) r i = localDefect A r i := by
  classical
  have hic : component A i = C := (component_eq_iff_mem A hC i).mpr i.2
  have hw : ∀ j ∉ C, shiftedColumn A r i j = 0 := by
    intro j hj
    apply shiftedColumn_eq_zero_outside
    intro hij
    exact hj (hic ▸ (mem_component A i j).mpr hij)
  have hinner : ∀ j : C,
      (∑ k : C, gram (matchedBlock A σ C) j k * shiftedColumn (matchedBlock A σ C) r i k) =
        ∑ k, gram A j k * shiftedColumn A r i k := by
    intro j
    simp only [matchedBlock_gram A hA σ hσ hC, matchedBlock_shiftedColumn A hA σ hσ hC]
    rw [sum_coe_sort C (fun k => gram A j k * shiftedColumn A r i k)]
    apply sum_subset (subset_univ _)
    intro k _ hk
    rw [hw k hk, mul_zero]
  unfold localDefect energy
  simp_rw [hinner]
  simp only [matchedBlock_shiftedColumn A hA σ hσ hC]
  rw [sum_coe_sort C (fun j => shiftedColumn A r i j * (r ^ 2 * shiftedColumn A r i j - ∑ k, gram A j k * shiftedColumn A r i k))]
  apply sum_subset (subset_univ _)
  intro j _ hj
  rw [hw j hj, zero_mul]

theorem matchedBlock_cycleCount (A : Matrix ι ι ℤ) (hA : Binary A)
    (σ : Equiv.Perm ι) (hσ : ∀ i, A i (σ i) = 1)
    {C : Finset ι} (hC : C ∈ components A) :
    cycleCount (matchedBlock A σ C) = cycleCountOn A C := by
  classical
  unfold cycleCount cycleCountOn
  have hw : ∀ i j : C, cycleWeight (matchedBlock A σ C) i j = cycleWeight A i j := by
    intro i j
    simp only [cycleWeight, matchedBlock_gram A hA σ hσ hC, Subtype.mk_lt_mk]
    rfl
  simp only [hw]
  rw [sum_coe_sort C (fun i => ∑ j : C, cycleWeight A i j)]
  apply sum_congr rfl
  intro i hi
  exact sum_coe_sort C (fun j => cycleWeight A i j)

theorem matchedBlock_det_ne_zero (A : Matrix ι ι ℤ) (hA : Binary A)
    (σ : Equiv.Perm ι) (hσ : ∀ i, A i (σ i) = 1) (hdet : A.det ≠ 0)
    {C : Finset ι} (hC : C ∈ components A) : (matchedBlock A σ C).det ≠ 0 := by
  have hp := determinant_matching_blocks A hA σ hσ
  have hn : (∏ C ∈ components A, |(matchedBlock A σ C).det|) ≠ 0 := by
    rw [← hp]
    exact abs_ne_zero.mpr hdet
  exact abs_ne_zero.mp ((prod_ne_zero_iff.mp hn) C hC)

end SparseComponent
