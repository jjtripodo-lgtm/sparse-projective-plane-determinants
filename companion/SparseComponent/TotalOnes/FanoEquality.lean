import SparseComponent.Extremizers
import SparseComponent.MatchingBlocks
import SparseComponent.TotalOnes.MatrixDefs
import SparseComponent.TotalOnes.Constants

/-!
Equality structure for the total-ones determinant theorem. Every set appearing
in `FanoBlockDecomposition` is a literal set of rows or support columns of the
original matrix. The predicate contains no determinant condition and no degree
or spectral assumption. The only forward determinant classification below with
a premise beyond `Binary` is explicitly labelled `of_regular`; global equality
regularity is established separately by the analytic and peeling arguments.
-/

namespace SparseComponent.TotalOnes
open Finset Matrix Real
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- An exhaustive, support-isolated decomposition into literal seven-by-seven
Fano incidence blocks. The empty index type gives the empty union. -/
structure FanoBlockDecomposition (A : Matrix ι ι ℤ) : Prop where
  rows_cover : (components A).biUnion id = univ
  columns_cover : (components A).biUnion (supportColumns A) = univ
  rows_disjoint : (↑(components A) : Set (Finset ι)).PairwiseDisjoint id
  columns_disjoint :
    (↑(components A) : Set (Finset ι)).PairwiseDisjoint (supportColumns A)
  blocks : ∀ C ∈ components A,
    C.card = 7 ∧ (supportColumns A C).card = 7 ∧
    (∀ i ∈ C, ∀ j ∈ C,
      (∑ k ∈ supportColumns A C, A i k * A j k) =
        (if i = j then (2 : ℤ) else 0) + 1) ∧
    (∀ i ∈ C, ∀ k ∉ supportColumns A C, A i k = 0) ∧
    (∀ i ∉ C, ∀ k ∈ supportColumns A C, A i k = 0)

/-- The explicit support partition is equivalent to the predecessor's literal
plane classification, without an extra degree or nonsingularity premise. -/
theorem fanoBlockDecomposition_iff_all_plane (A : Matrix ι ι ℤ) (hA : Binary A) :
    FanoBlockDecomposition A ↔ ∀ i, PlaneRows A 3 (component A i) := by
  classical
  constructor
  · intro hF i
    have h := hF.blocks (component A i) ((mem_components A _).mpr ⟨i, rfl⟩)
    refine ⟨by norm_num [h.1], ?_⟩
    intro j hj l hl
    have hg := h.2.2.1 j hj l hl
    rw [supportColumns_component, restricted_component_gram A hA i hj] at hg
    split_ifs at hg ⊢ <;> omega
  · intro hp
    have hd : ∀ i, rowDegree A i = 3 := all_plane_rowDegree A hA 3 hp
    have hc : ∀ k, columnDegree A k = 3 :=
      all_plane_columnDegree_unconditional A hA 3 hp
    refine ⟨components_union A, ?_, components_disjoint A,
      supportColumns_disjoint A hA, ?_⟩
    · ext k
      simp only [mem_biUnion, mem_univ, iff_true]
      have hn : (∑ i, A i k) ≠ 0 := by
        change columnDegree A k ≠ 0
        rw [hc k]
        norm_num
      obtain ⟨i, _, hi⟩ := exists_ne_zero_of_sum_ne_zero hn
      exact ⟨component A i, (mem_components A _).mpr ⟨i, rfl⟩,
        (mem_supportColumns A _ k).mpr
          ⟨i, self_mem_component A i, (hA i k).resolve_left hi⟩⟩
    · intro C hC
      obtain ⟨i, rfl⟩ := (mem_components A C).mp hC
      have h := literal_plane_component A hA 3 (by norm_num)
        (fun k => (hc k).le) (fun j => (hd j).le) i (hp i)
      rw [supportColumns_component]
      refine ⟨?_, ?_, ?_, h.2.2.2.1, h.2.2.2.2⟩
      · have hh := h.1
        norm_num at hh
        exact_mod_cast hh
      · have hh := h.1
        norm_num at hh
        rw [← h.2.1]
        exact_mod_cast hh
      · simpa using h.2.2.1

/-- A supplied isolated seven-row Fano block is exactly an actual row-overlap
component. Its columns may be given in any order; they are never changed. -/
theorem component_eq_of_isolated_fano_block (A : Matrix ι ι ℤ)
    (R C : Finset ι) (i : ι) (hi : i ∈ R)
    (hg : ∀ j ∈ R, ∀ l ∈ R,
      (∑ k ∈ C, A j k * A l k) = (if j = l then (2 : ℤ) else 0) + 1)
    (hout : ∀ j ∈ R, ∀ k ∉ C, A j k = 0)
    (hin : ∀ j ∉ R, ∀ k ∈ C, A j k = 0) : component A i = R := by
  classical
  have hgram : ∀ j ∈ R, ∀ l,
      gram A j l = ∑ k ∈ C, A j k * A l k := by
    intro j hj l
    symm
    apply sum_subset (subset_univ C)
    intro k _ hk
    rw [hout j hj k hk, zero_mul]
  have hzero : ∀ j ∈ R, ∀ l ∉ R, gram A j l = 0 := by
    intro j hj l hl
    rw [hgram j hj l]
    apply sum_eq_zero
    intro k hk
    rw [hin l hl k hk, mul_zero]
  ext j
  rw [mem_component]
  constructor
  · intro hij
    induction hij with
    | refl => exact hi
    | tail h hjk ih =>
      by_contra hk
      exact hjk (hzero _ ih _ hk)
  · intro hj
    apply Relation.ReflTransGen.single
    rw [hgram i hi j, hg i hi j hj]
    split_ifs <;> norm_num

/-- Arbitrary isolated seven-by-seven blocks covering the rows give the canonical
Fano decomposition. This is the reverse implication for an arbitrary disjoint
block presentation, without first assuming regularity or choosing a matching. -/
theorem fanoBlockDecomposition_of_isolated_blocks (A : Matrix ι ι ℤ) (hA : Binary A)
    (hcover : ∀ i, ∃ R C : Finset ι, i ∈ R ∧ R.card = 7 ∧ C.card = 7 ∧
      (∀ j ∈ R, ∀ l ∈ R,
        (∑ k ∈ C, A j k * A l k) = (if j = l then (2 : ℤ) else 0) + 1) ∧
      (∀ j ∈ R, ∀ k ∉ C, A j k = 0) ∧
      (∀ j ∉ R, ∀ k ∈ C, A j k = 0)) : FanoBlockDecomposition A := by
  classical
  apply (fanoBlockDecomposition_iff_all_plane A hA).mpr
  intro i
  obtain ⟨R, C, hi, hR, _hC, hg, hout, hin⟩ := hcover i
  rw [component_eq_of_isolated_fano_block A R C i hi hg hout hin]
  refine ⟨by norm_num [hR], ?_⟩
  intro j hj l hl
  have he : (∑ k ∈ C, A j k * A l k) = gram A j l := by
    apply sum_subset (subset_univ C)
    intro k _ hk
    rw [hout j hj k hk, zero_mul]
  rw [← he, hg j hj l hl]
  split_ifs <;> norm_num

/-- Regularity is derived from the structural predicate, not included in it. -/
theorem fanoBlockDecomposition_degrees (A : Matrix ι ι ℤ) (hA : Binary A)
    (hF : FanoBlockDecomposition A) :
    (∀ i, rowDegree A i = 3) ∧ (∀ j, columnDegree A j = 3) := by
  have hp := (fanoBlockDecomposition_iff_all_plane A hA).mp hF
  exact ⟨all_plane_rowDegree A hA 3 hp,
    all_plane_columnDegree_unconditional A hA 3 hp⟩

theorem edgeCount_eq_three_card_of_regular (A : Matrix ι ι ℤ)
    (hd : ∀ i, rowDegree A i = 3) :
    edgeCount A = 3 * (Fintype.card ι : ℤ) := by
  simp [edgeCount, hd, mul_comm]

theorem fanoBlockDecomposition_edgeCount (A : Matrix ι ι ℤ) (hA : Binary A)
    (hF : FanoBlockDecomposition A) :
    edgeCount A = 3 * (Fintype.card ι : ℤ) :=
  edgeCount_eq_three_card_of_regular A (fanoBlockDecomposition_degrees A hA hF).1

/-- A purely scalar identity for the exact Fano rate. -/
theorem exp_card_fanoRate (n : ℕ) :
    exp ((n : ℝ) * fanoRate) = (24 : ℝ) ^ ((n : ℝ) / 7) := by
  rw [rpow_def_of_pos (by norm_num : (0 : ℝ) < 24)]
  unfold fanoRate
  congr 1
  ring

/-- Structural reverse implication, with no supplied regularity or determinant
premise. Independent row/column permutations are already built into the sets. -/
theorem fanoBlockDecomposition_determinant_eq (A : Matrix ι ι ℤ) (hA : Binary A)
    (hF : FanoBlockDecomposition A) :
    |(A.det : ℝ)| = (24 : ℝ) ^ ((Fintype.card ι : ℝ) / 7) := by
  have hp := (fanoBlockDecomposition_iff_all_plane A hA).mp hF
  obtain ⟨hd, hc⟩ := fanoBlockDecomposition_degrees A hA hF
  have h := all_plane_determinant_eq A hA 3 (by norm_num)
    (fun k => (hc k).le) (fun i => (hd i).le) hp
  norm_num [designBlockDet_three, planeOrder] at h
  exact h

/-- Every disjoint Fano union also attains the exact total-ones exponent. -/
theorem fanoBlockDecomposition_total_ones_equality (A : Matrix ι ι ℤ)
    (hA : Binary A) (hF : FanoBlockDecomposition A) :
    |(A.det : ℝ)| = exp ((Fintype.card ι : ℝ) * fanoRate +
      edgeSlope * ((edgeCount A : ℝ) - 3 * (Fintype.card ι : ℝ))) := by
  rw [fanoBlockDecomposition_edgeCount A hA hF]
  simp only [Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, sub_self,
    mul_zero, add_zero, exp_card_fanoRate]
  exact fanoBlockDecomposition_determinant_eq A hA hF

/-- Conditional forward bridge: the separate global theorem must supply the
actual row and column degree equalities. No degree caps are silently assumed. -/
theorem total_ones_equality_iff_fano_of_regular (A : Matrix ι ι ℤ) (hA : Binary A)
    (hd : ∀ i, rowDegree A i = 3) (hc : ∀ j, columnDegree A j = 3) :
    (|(A.det : ℝ)| = exp ((Fintype.card ι : ℝ) * fanoRate +
      edgeSlope * ((edgeCount A : ℝ) - 3 * (Fintype.card ι : ℝ)))) ↔
    FanoBlockDecomposition A := by
  rw [edgeCount_eq_three_card_of_regular A hd]
  simp only [Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, sub_self,
    mul_zero, add_zero, exp_card_fanoRate]
  rw [fanoBlockDecomposition_iff_all_plane A hA]
  have h := determinant_attains_iff_all_plane A hA 3 (by norm_num)
    (fun j => (hc j).le) (fun i => (hd i).le)
  norm_num [designBlockDet_three, planeOrder] at h
  exact h

/-- The canonical support blocks really occur as a block diagonal matrix under
exhaustive independent row and column permutations; the residual block is empty. -/
theorem fanoBlockDecomposition_literal_blocks (A : Matrix ι ι ℤ) (hA : Binary A)
    (hF : FanoBlockDecomposition A) :
    badRows A 3 = ∅ ∧ badColumns A 3 = ∅ ∧
    A.submatrix (rowReindex A 3) (columnReindex A hA 3) =
      Matrix.blockDiagonal' (fun b : BlockLabel A 3 =>
        A.submatrix (fun i : blockRows A 3 b => i.1)
          (fun k : blockColumns A 3 b => k.1)) := by
  classical
  have hp := (fanoBlockDecomposition_iff_all_plane A hA).mp hF
  have hr : badRows A 3 = ∅ := by simp [badRows, hp]
  have hd := (fanoBlockDecomposition_degrees A hA hF).1
  have hc := (fanoBlockDecomposition_degrees A hA hF).2
  have hm := residual_row_column_card_match A hA 3 (by norm_num)
    (fun k => (hc k).le) (fun i => (hd i).le)
  rw [hr, card_empty] at hm
  exact ⟨hr, card_eq_zero.mp hm.symm, literal_block_decomposition A hA 3⟩

/-- Counting the literal components shows that the order is a multiple of seven. -/
theorem fanoBlockDecomposition_card (A : Matrix ι ι ℤ)
    (hF : FanoBlockDecomposition A) :
    Fintype.card ι = 7 * (components A).card := by
  classical
  have h := sum_components A (fun _ => (1 : ℤ))
  simp only [sum_const, nsmul_eq_mul, mul_one, card_univ] at h
  have hb : ∀ C ∈ components A, (C.card : ℤ) = 7 := by
    intro C hC
    rw [(hF.blocks C hC).1]
    norm_num
  rw [sum_congr rfl hb] at h
  simp only [sum_const, nsmul_eq_mul] at h
  exact_mod_cast (by linarith : (Fintype.card ι : ℤ) = 7 * (components A).card)

/-- Exact product of one determinant-24 factor for each actual support block. -/
theorem fanoBlockDecomposition_determinant_product (A : Matrix ι ι ℤ)
    (hA : Binary A) (hF : FanoBlockDecomposition A) :
    |A.det| = ∏ _C ∈ components A, (24 : ℤ) := by
  classical
  have h := fanoBlockDecomposition_determinant_eq A hA hF
  rw [fanoBlockDecomposition_card A hF] at h
  push_cast at h
  have he : (7 * ((components A).card : ℝ)) / 7 = (components A).card := by ring
  rw [he, rpow_natCast] at h
  have hi : |A.det| = (24 : ℤ) ^ (components A).card := by exact_mod_cast h
  simpa using hi

/-- A support matching exposes literal square submatrices, each of determinant
absolute value 24, whose determinant product is exactly that of the input. -/
theorem fanoBlockDecomposition_matched_determinants (A : Matrix ι ι ℤ)
    (hA : Binary A) (hF : FanoBlockDecomposition A) :
    ∃ σ : Equiv.Perm ι, (∀ i, A i (σ i) = 1) ∧
      (∀ C ∈ components A, |(matchedBlock A σ C).det| = 24) ∧
      |A.det| = ∏ C ∈ components A, |(matchedBlock A σ C).det| := by
  classical
  have hp := (fanoBlockDecomposition_iff_all_plane A hA).mp hF
  obtain ⟨hd, hc⟩ := fanoBlockDecomposition_degrees A hA hF
  have hdet : A.det ≠ 0 := by
    intro hz
    have he := fanoBlockDecomposition_determinant_eq A hA hF
    rw [hz, Int.cast_zero, abs_zero] at he
    exact (ne_of_gt (rpow_pos_of_pos (by norm_num : (0 : ℝ) < 24)
      ((Fintype.card ι : ℝ) / 7))) he.symm
  obtain ⟨σ, hσ⟩ := exists_support_matching A hA hdet
  refine ⟨σ, hσ, ?_, determinant_matching_blocks A hA σ hσ⟩
  intro C hC
  let B := matchedBlock A σ C
  have hB : Binary B := matchedBlock_binary A hA σ C
  have hg : ∀ i j : C, gram B i j = if i = j then 3 else 1 := by
    intro i j
    rw [matchedBlock_gram A hA σ hσ hC]
    have hCp : PlaneRows A 3 C := by
      obtain ⟨k, rfl⟩ := (mem_components A C).mp hC
      exact hp k
    rw [hCp.2 i i.2 j j.2]
    simp only [Subtype.ext_iff]
  have hcomponent : ∀ i : C, component B i = univ := by
    intro i
    ext j
    simp only [mem_component, mem_univ, iff_true]
    apply Relation.ReflTransGen.single
    rw [hg]
    split_ifs <;> norm_num
  have hBP : ∀ i, PlaneRows B 3 (component B i) := by
    intro i
    rw [hcomponent]
    refine ⟨?_, fun j _ k _ => hg j k⟩
    norm_num [Fintype.card_coe, (hF.blocks C hC).1]
  have hBF := (fanoBlockDecomposition_iff_all_plane B hB).mpr hBP
  have he := fanoBlockDecomposition_determinant_eq B hB hBF
  norm_num [Fintype.card_coe, (hF.blocks C hC).1] at he
  exact_mod_cast he

/-- Empty matrices are included as the empty union, with no special convention
added to the structural predicate. -/
theorem empty_fanoBlockDecomposition (A : Matrix (Fin 0) (Fin 0) ℤ)
    (hA : Binary A) : FanoBlockDecomposition A := by
  apply (fanoBlockDecomposition_iff_all_plane A hA).mpr
  intro i
  exact Fin.elim0 i

end SparseComponent.TotalOnes
