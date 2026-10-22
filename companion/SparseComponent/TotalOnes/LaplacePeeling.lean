import SparseComponent.TotalOnes.MatrixDefs
import SparseComponent.TotalOnes.Constants
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
Literal deletion and conditional induction for the fixed total-ones exponent.
The induction results in this file explicitly assume a minimum-degree theorem;
they are not, by themselves, the full sparse determinant theorem.
-/

namespace SparseComponent.TotalOnes
open Finset Matrix

section Degrees
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
/-- Transposition preserves the literal zero-one condition. -/
theorem binary_transpose (A : Matrix ι ι ℤ) (hA : Binary A) : Binary A.transpose :=
  fun i j => hA j i

@[simp] theorem rowDegree_transpose (A : Matrix ι ι ℤ) (i : ι) :
    rowDegree A.transpose i = columnDegree A i := rfl

@[simp] theorem columnDegree_transpose (A : Matrix ι ι ℤ) (j : ι) :
    columnDegree A.transpose j = rowDegree A j := rfl

@[simp] theorem edgeCount_transpose (A : Matrix ι ι ℤ) :
    edgeCount A.transpose = edgeCount A := by
  unfold edgeCount rowDegree
  exact sum_comm

theorem rowDegree_nonneg (A : Matrix ι ι ℤ) (hA : Binary A) (i : ι) :
    0 ≤ rowDegree A i :=
  sum_nonneg (fun j _ => binary_nonneg A hA i j)

theorem columnDegree_nonneg (A : Matrix ι ι ℤ) (hA : Binary A) (j : ι) :
    0 ≤ columnDegree A j :=
  sum_nonneg (fun i _ => binary_nonneg A hA i j)

/-- A nonsingular binary matrix has no zero-degree row. -/
theorem rowDegree_pos_of_det_ne_zero [DecidableEq ι] (A : Matrix ι ι ℤ) (hA : Binary A)
    (hdet : A.det ≠ 0) (i : ι) : 0 < rowDegree A i := by
  have hn := rowDegree_nonneg A hA i
  by_contra h
  have hz : rowDegree A i = 0 := by omega
  have hrow : ∀ j, A i j = 0 := by
    intro j
    exact (sum_eq_zero_iff_of_nonneg (fun k _ => binary_nonneg A hA i k)).mp hz
      j (mem_univ j)
  exact hdet (Matrix.det_eq_zero_of_row_eq_zero i hrow)

/-- The column version is obtained by actual transposition. -/
theorem columnDegree_pos_of_det_ne_zero [DecidableEq ι] (A : Matrix ι ι ℤ) (hA : Binary A)
    (hdet : A.det ≠ 0) (j : ι) : 0 < columnDegree A j := by
  exact rowDegree_pos_of_det_ne_zero A.transpose (binary_transpose A hA)
    (by simpa only [Matrix.det_transpose] using hdet) j

/-- Degree one means that there is a unique actual unit entry in the row. -/
theorem rowDegree_one_support (A : Matrix ι ι ℤ) (hA : Binary A) (i : ι)
    (hi : rowDegree A i = 1) :
    ∃ j, A i j = 1 ∧ ∀ k, k ≠ j → A i k = 0 := by
  classical
  have hex : ∃ j, A i j = 1 := by
    by_contra h
    have hz : ∀ j, A i j = 0 := by
      intro j
      rcases hA i j with hj | hj
      · exact hj
      · exact False.elim (h ⟨j, hj⟩)
    simp [rowDegree, hz] at hi
  obtain ⟨j, hj⟩ := hex
  refine ⟨j, hj, ?_⟩
  have hs : ∑ k ∈ univ.erase j, A i k = 0 := by
    have he := sum_erase_add univ (fun k => A i k) (mem_univ j)
    change (∑ k ∈ univ.erase j, A i k) + A i j = rowDegree A i at he
    rw [hj, hi] at he
    omega
  intro k hkj
  exact (sum_eq_zero_iff_of_nonneg (fun k _ => binary_nonneg A hA i k)).mp hs
    k (mem_erase.mpr ⟨hkj, mem_univ k⟩)

end Degrees

section LiteralPeel
variable {n : ℕ}

/-- Delete the indicated literal row and column, keeping the induced order. -/
def laplaceMinor (A : Matrix (Fin (n+1)) (Fin (n+1)) ℤ)
    (i j : Fin (n+1)) : Matrix (Fin n) (Fin n) ℤ :=
  A.submatrix i.succAbove j.succAbove

theorem laplaceMinor_binary (A : Matrix (Fin (n+1)) (Fin (n+1)) ℤ)
    (hA : Binary A) (i j : Fin (n+1)) : Binary (laplaceMinor A i j) :=
  fun a b => hA (i.succAbove a) (j.succAbove b)

/-- Cofactor expansion along an arbitrary row with one nonzero unit. -/
theorem det_eq_sign_laplaceMinor (A : Matrix (Fin (n+1)) (Fin (n+1)) ℤ)
    (i j : Fin (n+1)) (hij : A i j = 1)
    (hz : ∀ k, k ≠ j → A i k = 0) :
    A.det = (-1 : ℤ)^((i : ℕ)+(j : ℕ)) * (laplaceMinor A i j).det := by
  rw [Matrix.det_succ_row A i, sum_eq_single j]
  · simp only [hij, mul_one, laplaceMinor]
  · intro k _ hkj
    simp only [hz k hkj, mul_zero, zero_mul]
  · simp

/-- Literal unit-row deletion preserves the absolute integer determinant. -/
theorem abs_det_laplaceMinor (A : Matrix (Fin (n+1)) (Fin (n+1)) ℤ)
    (i j : Fin (n+1)) (hij : A i j = 1)
    (hz : ∀ k, k ≠ j → A i k = 0) :
    |(laplaceMinor A i j).det| = |A.det| := by
  rw [det_eq_sign_laplaceMinor A i j hij hz, abs_mul, abs_pow]
  simp

/-- The same identity in the codomain of the final determinant inequality. -/
theorem abs_real_det_laplaceMinor (A : Matrix (Fin (n+1)) (Fin (n+1)) ℤ)
    (i j : Fin (n+1)) (hij : A i j = 1)
    (hz : ∀ k, k ≠ j → A i k = 0) :
    |((laplaceMinor A i j).det : ℝ)| = |(A.det : ℝ)| := by
  exact_mod_cast abs_det_laplaceMinor A i j hij hz

/-- Removing a unit row removes exactly the actual incident column degree. -/
theorem edgeCount_laplaceMinor (A : Matrix (Fin (n+1)) (Fin (n+1)) ℤ)
    (i j : Fin (n+1)) (hz : ∀ k, k ≠ j → A i k = 0) :
    edgeCount (laplaceMinor A i j) = edgeCount A - columnDegree A j := by
  have he : edgeCount A = columnDegree A j + edgeCount (laplaceMinor A i j) := by
    calc
      edgeCount A = ∑ b, ∑ a, A a b := by
        unfold edgeCount rowDegree
        exact sum_comm
      _ = columnDegree A j + ∑ b : Fin n, ∑ a, A a (j.succAbove b) :=
        Fin.sum_univ_succAbove (fun b => ∑ a, A a b) j
      _ = columnDegree A j + ∑ b : Fin n, ∑ a : Fin n,
          A (i.succAbove a) (j.succAbove b) := by
        congr 1
        apply sum_congr rfl
        intro b _
        rw [Fin.sum_univ_succAbove (fun a => A a (j.succAbove b)) i,
          hz _ (Fin.succAbove_ne j b), zero_add]
      _ = columnDegree A j + edgeCount (laplaceMinor A i j) := by
        congr 1
        unfold edgeCount rowDegree laplaceMinor
        exact sum_comm
  omega

/-- The removed column has at least its one entry in the removed row. -/
theorem incident_columnDegree_ge_one (A : Matrix (Fin (n+1)) (Fin (n+1)) ℤ)
    (hA : Binary A) (i j : Fin (n+1)) (hij : A i j = 1) :
    1 ≤ columnDegree A j := by
  have h := single_le_sum (f := fun a => A a j)
    (fun a _ => binary_nonneg A hA a j) (mem_univ i)
  simpa only [hij, columnDegree] using h

/-- The fixed exponent gains more than 1/20 at every peel, even when the
incident column also has degree one. No maximum-degree assumption is used. -/
theorem laplaceMinor_exponent_gap (A : Matrix (Fin (n+1)) (Fin (n+1)) ℤ)
    (hA : Binary A) (i j : Fin (n+1)) (hij : A i j = 1)
    (hz : ∀ k, k ≠ j → A i k = 0) :
    (n : ℝ)*fanoRate + edgeSlope*((edgeCount (laplaceMinor A i j) : ℝ)-3*(n : ℝ))
      + 1/20 <
    ((n+1 : ℕ) : ℝ)*fanoRate + edgeSlope*((edgeCount A : ℝ)-3*((n+1 : ℕ) : ℝ)) := by
  have hk : (1 : ℝ) ≤ (columnDegree A j : ℝ) := by
    exact_mod_cast incident_columnDegree_ge_one A hA i j hij
  have hd : (edgeCount (laplaceMinor A i j) : ℝ) =
      (edgeCount A : ℝ) - (columnDegree A j : ℝ) := by
    exact_mod_cast edgeCount_laplaceMinor A i j hz
  have hm := mul_nonneg (le_of_lt edgeSlope_pos) (sub_nonneg.mpr hk)
  push_cast
  rw [hd]
  nlinarith [peeling_margin]

/-- A determinant bound for the smaller literal minor is strictly below the
fixed exponent for its parent matrix. -/
theorem row_peel_strict (A : Matrix (Fin (n+1)) (Fin (n+1)) ℤ)
    (hA : Binary A) (i : Fin (n+1)) (hi : rowDegree A i = 1)
    (hsmall : ∀ B : Matrix (Fin n) (Fin n) ℤ, Binary B →
      |(B.det : ℝ)| ≤ Real.exp ((n : ℝ)*fanoRate +
        edgeSlope*((edgeCount B : ℝ)-3*(n : ℝ)))) :
    |(A.det : ℝ)| < Real.exp (((n+1 : ℕ) : ℝ)*fanoRate +
      edgeSlope*((edgeCount A : ℝ)-3*((n+1 : ℕ) : ℝ))) := by
  obtain ⟨j, hij, hz⟩ := rowDegree_one_support A hA i hi
  have hb := hsmall (laplaceMinor A i j) (laplaceMinor_binary A hA i j)
  rw [abs_real_det_laplaceMinor A i j hij hz] at hb
  apply lt_of_le_of_lt hb
  apply Real.exp_lt_exp.mpr
  linarith [laplaceMinor_exponent_gap A hA i j hij hz]

/-- The column-degree-one branch uses the transpose of the actual input. -/
theorem column_peel_strict (A : Matrix (Fin (n+1)) (Fin (n+1)) ℤ)
    (hA : Binary A) (j : Fin (n+1)) (hj : columnDegree A j = 1)
    (hsmall : ∀ B : Matrix (Fin n) (Fin n) ℤ, Binary B →
      |(B.det : ℝ)| ≤ Real.exp ((n : ℝ)*fanoRate +
        edgeSlope*((edgeCount B : ℝ)-3*(n : ℝ)))) :
    |(A.det : ℝ)| < Real.exp (((n+1 : ℕ) : ℝ)*fanoRate +
      edgeSlope*((edgeCount A : ℝ)-3*((n+1 : ℕ) : ℝ))) := by
  simpa only [Matrix.det_transpose, edgeCount_transpose] using
    row_peel_strict A.transpose (binary_transpose A hA) j hj hsmall

end LiteralPeel

/-- Explicitly conditional all-order transfer. The premise must be discharged
by the genuine minimum-degree theorem before obtaining a full sparse bound. -/
theorem conditional_all_orders_bound
    (hmin : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ), Binary A → A.det ≠ 0 →
      (∀ i, 2 ≤ rowDegree A i) → (∀ j, 2 ≤ columnDegree A j) →
      |(A.det : ℝ)| ≤ Real.exp ((n : ℝ)*fanoRate +
        edgeSlope*((edgeCount A : ℝ)-3*(n : ℝ))))
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) (hA : Binary A) :
    |(A.det : ℝ)| ≤ Real.exp ((n : ℝ)*fanoRate +
      edgeSlope*((edgeCount A : ℝ)-3*(n : ℝ))) := by
  induction n with
  | zero => simp [edgeCount]
  | succ n ih =>
    by_cases hd : A.det = 0
    · simpa only [hd, Int.cast_zero, abs_zero] using
        (le_of_lt (Real.exp_pos (((n+1 : ℕ) : ℝ)*fanoRate +
          edgeSlope*((edgeCount A : ℝ)-3*((n+1 : ℕ) : ℝ)))))
    by_cases hr : ∀ i, 2 ≤ rowDegree A i
    · by_cases hc : ∀ j, 2 ≤ columnDegree A j
      · exact hmin (n+1) A hA hd hr hc
      · obtain ⟨j, hj⟩ := not_forall.mp hc
        have hp := columnDegree_pos_of_det_ne_zero A hA hd j
        have hj' : columnDegree A j = 1 := by omega
        exact le_of_lt (column_peel_strict A hA j hj' ih)
    · obtain ⟨i, hi⟩ := not_forall.mp hr
      have hp := rowDegree_pos_of_det_ne_zero A hA hd i
      have hi' : rowDegree A i = 1 := by omega
      exact le_of_lt (row_peel_strict A hA i hi' ih)

/-- Explicitly conditional equality transfer. Strictness of every peel excludes
all low-degree equality cases; the empty matrix retains its vacuous regularity. -/
theorem conditional_all_orders_equality_regularity
    (hmin : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ), Binary A → A.det ≠ 0 →
      (∀ i, 2 ≤ rowDegree A i) → (∀ j, 2 ≤ columnDegree A j) →
      |(A.det : ℝ)| ≤ Real.exp ((n : ℝ)*fanoRate +
        edgeSlope*((edgeCount A : ℝ)-3*(n : ℝ))))
    (heqmin : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ), Binary A → A.det ≠ 0 →
      (∀ i, 2 ≤ rowDegree A i) → (∀ j, 2 ≤ columnDegree A j) →
      |(A.det : ℝ)| = Real.exp ((n : ℝ)*fanoRate +
        edgeSlope*((edgeCount A : ℝ)-3*(n : ℝ))) →
      (∀ i, rowDegree A i = 3) ∧ (∀ j, columnDegree A j = 3))
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) (hA : Binary A)
    (heq : |(A.det : ℝ)| = Real.exp ((n : ℝ)*fanoRate +
      edgeSlope*((edgeCount A : ℝ)-3*(n : ℝ)))) :
    (∀ i, rowDegree A i = 3) ∧ (∀ j, columnDegree A j = 3) := by
  have hd : A.det ≠ 0 := by
    intro hz
    have hp := Real.exp_pos ((n : ℝ)*fanoRate +
      edgeSlope*((edgeCount A : ℝ)-3*(n : ℝ)))
    simp only [hz, Int.cast_zero, abs_zero] at heq
    linarith
  cases n with
  | zero => exact ⟨fun i => Fin.elim0 i, fun j => Fin.elim0 j⟩
  | succ n =>
    have hsmall := conditional_all_orders_bound hmin n
    have hr : ∀ i, 2 ≤ rowDegree A i := by
      intro i
      have hp := rowDegree_pos_of_det_ne_zero A hA hd i
      by_contra hi
      have hi' : rowDegree A i = 1 := by omega
      exact (ne_of_lt (row_peel_strict A hA i hi' hsmall)) heq
    have hc : ∀ j, 2 ≤ columnDegree A j := by
      intro j
      have hp := columnDegree_pos_of_det_ne_zero A hA hd j
      by_contra hj
      have hj' : columnDegree A j = 1 := by omega
      exact (ne_of_lt (column_peel_strict A hA j hj' hsmall)) heq
    exact heqmin (n+1) A hA hd hr hc heq

end SparseComponent.TotalOnes
