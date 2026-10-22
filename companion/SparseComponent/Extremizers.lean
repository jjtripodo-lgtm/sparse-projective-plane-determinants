import SparseComponent.Corollaries

namespace SparseComponent
open Finset Matrix Real
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

theorem all_plane_totalDefect_zero (A : Matrix ι ι ℤ) (r : ℤ)
    (hp : ∀ i, PlaneRows A r (component A i)) : totalDefect A r = 0 :=
  sum_eq_zero (fun i _ => plane_localDefect_zero A r i (hp i))

theorem all_plane_rowDegree (A : Matrix ι ι ℤ) (hA : Binary A) (r : ℤ)
    (hp : ∀ i, PlaneRows A r (component A i)) (i : ι) : rowDegree A i = r := by
  have h := (hp i).2 i (self_mem_component A i) i (self_mem_component A i)
  simpa [gram_diagonal A hA] using h

theorem all_plane_cycleCount_zero (A : Matrix ι ι ℤ) (r : ℤ)
    (hp : ∀ i, PlaneRows A r (component A i)) : cycleCount A = 0 := by
  apply sum_eq_zero
  intro i hi
  apply sum_eq_zero
  intro j hj
  unfold cycleWeight
  split_ifs with hij
  · by_cases hconn : Connected (gram A) i j
    · rw [(hp i).2 i (self_mem_component A i) j ((mem_component A i j).mpr hconn), if_neg (ne_of_lt hij)]
      norm_num [chooseTwo]
    · rw [gram_eq_zero_of_not_connected A hconn]
      norm_num [chooseTwo]
  · rfl

theorem all_plane_columnDegree (A : Matrix ι ι ℤ) (hA : Binary A) (r : ℤ)
    (hr : 2 ≤ r) (hc : ∀ k, columnDegree A k ≤ r) (hd : ∀ i, rowDegree A i ≤ r)
    (hp : ∀ i, PlaneRows A r (component A i)) (k : ι) : columnDegree A k = r := by
  have hs : (∑ k : ι, (r - columnDegree A k)) = 0 := by
    rw [sum_sub_distrib, ← row_column_degree_sum A]
    simp [all_plane_rowDegree A hA r hp]
  have hz := (sum_eq_zero_iff_of_nonneg (fun k _ => sub_nonneg.mpr (hc k))).mp hs k (mem_univ k)
  omega

/-- Exact plane components force column regularity even before imposing degree caps. -/
theorem all_plane_columnDegree_unconditional (A : Matrix ι ι ℤ) (hA : Binary A) (r : ℤ)
    (hp : ∀ i, PlaneRows A r (component A i)) (k : ι) : columnDegree A k = r := by
  have hs : (∑ k, columnDegree A k) = Fintype.card ι * r := by
    rw [← row_column_degree_sum A]
    simp [all_plane_rowDegree A hA r hp]
  have hsq : (∑ k, columnDegree A k ^ 2) = Fintype.card ι * r ^ 2 := by
    rw [← sum_gram_eq_column_squares A]
    change (∑ i, rowSum (gram A) i) = _
    have he : ∀ i, rowSum (gram A) i = r ^ 2 :=
      fun i => plane_gram_rowSum A r i (hp i) (self_mem_component A i)
    simp [he]
  have hz : (∑ k, (columnDegree A k - r) ^ 2) = 0 := by
    simp_rw [show ∀ k, (columnDegree A k - r) ^ 2 =
      columnDegree A k ^ 2 - 2 * r * columnDegree A k + r ^ 2 by intro k; ring]
    simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, nsmul_eq_mul, card_univ, hs, hsq]
    ring
  have hk := (sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg (columnDegree A k - r))).mp hz k (mem_univ k)
  nlinarith [sq_nonneg (columnDegree A k - r)]

/-- A zero total defect pins every actual eigenvalue to the two interpolation nodes. -/
theorem zero_totalDefect_eigenvalues (A : Matrix ι ι ℤ) (hA : Binary A)
    (r : ℕ) (hr : 2 ≤ r) (hc : ∀ k, columnDegree A k ≤ r) (hd : ∀ i, rowDegree A i ≤ r)
    (hT : totalDefect A r = 0) (i : ι) : eigenvalues A i = (r : ℝ) - 1 ∨ eigenvalues A i = (r : ℝ) ^ 2 := by
  have hs := eigenvalues_cubic_sum A (r : ℤ)
  simp only [Int.cast_natCast, hT, Int.cast_zero] at hs
  have hn : ∀ j, 0 ≤ (eigenvalues A j - ((r : ℝ) - 1)) ^ 2 * ((r : ℝ) ^ 2 - eigenvalues A j) := by
    intro j
    apply mul_nonneg (sq_nonneg _)
    apply sub_nonneg.mpr
    simpa using eigenvalues_cap A hA (r : ℤ) (by positivity) hc hd j
  have hi := (sum_eq_zero_iff_of_nonneg (fun j _ => hn j)).mp hs i (mem_univ i)
  rcases mul_eq_zero.mp hi with h | h
  · left
    nlinarith [sq_nonneg (eigenvalues A i - ((r : ℝ) - 1))]
  · right
    linarith

theorem zero_totalDefect_det_ne_zero (A : Matrix ι ι ℤ) (hA : Binary A)
    (r : ℕ) (hr : 2 ≤ r) (hc : ∀ k, columnDegree A k ≤ r) (hd : ∀ i, rowDegree A i ≤ r)
    (hT : totalDefect A r = 0) : A.det ≠ 0 := by
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hpos : ∀ i, 0 < eigenvalues A i := by
    intro i
    rcases zero_totalDefect_eigenvalues A hA r hr hc hd hT i with h | h
    · rw [h]; linarith
    · rw [h]; positivity
  have hprod : (0 : ℝ) < ∏ i, eigenvalues A i := prod_pos (fun i _ => hpos i)
  have hdet := (realGram_posSemidef A).isHermitian.det_eq_prod_eigenvalues
  simp only [RCLike.ofReal_real_eq_id, id_eq] at hdet
  change (realGram A).det = ∏ i, eigenvalues A i at hdet
  rw [← hdet, realGram_det] at hprod
  intro hzero
  simp [hzero] at hprod

/-- Exact plane components attain the block determinant constant. -/
theorem all_plane_determinant_eq (A : Matrix ι ι ℤ) (hA : Binary A)
    (r : ℕ) (hr : 2 ≤ r) (hc : ∀ k, columnDegree A k ≤ r) (hd : ∀ i, rowDegree A i ≤ r)
    (hp : ∀ i, PlaneRows A r (component A i)) :
    |(A.det : ℝ)| = designBlockDet r ^ ((Fintype.card ι : ℝ) / planeOrder r) := by
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have ht : (0 : ℝ) < r - 1 := by linarith
  have htR : (r : ℝ) - 1 < (r : ℝ) ^ 2 := by nlinarith
  have hT := all_plane_totalDefect_zero A r hp
  have hdet := zero_totalDefect_det_ne_zero A hA r hr hc hd hT
  have hrow := all_plane_rowDegree A hA r hp
  have hcol := all_plane_columnDegree A hA r (by exact_mod_cast hr) hc hd hp
  have hcycle := all_plane_cycleCount_zero A r hp
  have hlog : ∀ i, log (eigenvalues A i) =
      logA ((r : ℝ) - 1) ((r : ℝ) ^ 2) + logB ((r : ℝ) - 1) ((r : ℝ) ^ 2) * eigenvalues A i -
        gamma r * eigenvalues A i ^ 2 := by
    intro i
    rcases zero_totalDefect_eigenvalues A hA r hr hc hd hT i with h | h
    · rw [h]
      have h := log_interpolation_t ((r : ℝ) - 1) ((r : ℝ) ^ 2) ht
      unfold quadratic at h
      simpa only [gamma, neg_mul, sub_eq_add_neg] using h.symm
    · rw [h]
      have h := log_interpolation_R ((r : ℝ) - 1) ((r : ℝ) ^ 2) ht htR
      unfold quadratic at h
      simpa only [gamma, neg_mul, sub_eq_add_neg] using h.symm
  have hsum := sum_congr (s₁ := (univ : Finset ι)) rfl (fun i _ => hlog i)
  rw [eigenvalues_log_sum A hdet] at hsum
  simp only [sum_sub_distrib, sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul, card_univ,
    eigenvalues_sum A hA, eigenvalues_square_sum A, trace_gram_square A hA] at hsum
  simp only [hrow, hcol, hcycle, sum_const, nsmul_eq_mul, card_univ,
    Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_natCast, Int.cast_ofNat, Int.cast_zero] at hsum
  have hb := congrArg (fun x : ℝ => (Fintype.card ι : ℝ) * x) (base_polynomial_value r hrR)
  have hl : log |(A.det : ℝ)| = (Fintype.card ι : ℝ) * blockLogRate r := by
    nlinarith [hb]
  rw [rpow_def_of_pos (designBlockDet_positive r hrR)]
  rw [← exp_log (abs_pos.mpr (by exact_mod_cast hdet)), hl, ← designBlockDet_log r hrR]
  congr 1
  ring

theorem residualRows_zero_iff (A : Matrix ι ι ℤ) (r : ℤ) :
    residualRows A r = 0 ↔ ∀ i, PlaneRows A r (component A i) := by
  classical
  constructor
  · intro h i
    unfold residualRows at h
    have hc : (badRows A r).card = 0 := by exact_mod_cast h
    have he := card_eq_zero.mp hc
    by_contra hi
    have hm : i ∈ badRows A r := by simp [badRows, hi]
    rw [he] at hm
    simp at hm
  · intro h
    simp [residualRows, badRows, h]

/-- Equality in the sharp plane-block determinant constant occurs exactly for literal plane sums. -/
theorem determinant_attains_iff_all_plane (A : Matrix ι ι ℤ) (hA : Binary A)
    (r : ℕ) (hr : 2 ≤ r) (hc : ∀ k, columnDegree A k ≤ r) (hd : ∀ i, rowDegree A i ≤ r) :
    |(A.det : ℝ)| = designBlockDet r ^ ((Fintype.card ι : ℝ) / planeOrder r) ↔
      ∀ i, PlaneRows A r (component A i) := by
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  constructor
  · intro heq
    have hb := rpow_pos_of_pos (designBlockDet_positive r hrR)
      ((Fintype.card ι : ℝ) / planeOrder r)
    have hdet : A.det ≠ 0 := by
      intro hz
      simp only [hz, Int.cast_zero, abs_zero] at heq
      linarith
    apply (residualRows_zero_iff A r).mp
    have h := residualRows_le_log_deficit A hA hdet r hr hc hd
    rw [heq, log_rpow (designBlockDet_positive r hrR)] at h
    have hz : (residualRows A r : ℝ) = 0 := by
      have hn : (0 : ℝ) ≤ (residualRows A r : ℝ) := by unfold residualRows; positivity
      nlinarith
    exact_mod_cast hz
  · exact all_plane_determinant_eq A hA r hr hc hd

end SparseComponent
