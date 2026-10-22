import SparseComponent.TotalFamily.Edge
import SparseComponent.TotalOnes.LaplacePeeling

namespace SparseComponent.TotalFamily
open Finset Matrix Real TotalOnes

noncomputable def exponent (r : ℝ) (n : ℕ) (e : ℤ) : ℝ :=
  (n:ℝ)*rate r + slope r*((e:ℝ)-r*(n:ℝ))

/-- Every cofactor minor removes the whole selected row, regardless of its degree. -/
theorem minor_edgeCount_le {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℤ)
    (hA : Binary A) (i j : Fin (n+1)) :
    edgeCount (laplaceMinor A i j) ≤ edgeCount A - rowDegree A i := by
  have hrow (a : Fin n) : (∑ b : Fin n, A (i.succAbove a) (j.succAbove b)) ≤
      rowDegree A (i.succAbove a) := by
    unfold rowDegree
    rw [Fin.sum_univ_succAbove (fun b => A (i.succAbove a) b) j]
    linarith [binary_nonneg A hA (i.succAbove a) j]
  have h := sum_le_sum (s := (univ : Finset (Fin n))) fun a _ => hrow a
  have he : edgeCount A = rowDegree A i + ∑ a : Fin n, rowDegree A (i.succAbove a) :=
    Fin.sum_univ_succAbove (rowDegree A) i
  change edgeCount (laplaceMinor A i j) ≤ _ at h
  omega

/-- Absolute Laplace expansion of the original binary matrix. -/
theorem abs_det_le_cofactors {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℤ)
    (hA : Binary A) (i : Fin (n+1)) :
    |(A.det:ℝ)| ≤ ∑ j, (A i j:ℝ)*|((laplaceMinor A i j).det:ℝ)| := by
  calc
    |(A.det:ℝ)| = |∑ j : Fin (n+1), (-1:ℝ)^((i:ℕ)+(j:ℕ))*(A i j:ℝ)*((laplaceMinor A i j).det:ℝ)| := by
      rw [Matrix.det_succ_row A i]
      simp only [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, laplaceMinor]
    _ ≤ ∑ j : Fin (n+1), |(-1:ℝ)^((i:ℕ)+(j:ℕ))*(A i j:ℝ)*((laplaceMinor A i j).det:ℝ)| :=
      abs_sum_le_sum_abs _ _
    _ = _ := by
      apply sum_congr rfl
      intro j _
      rw [abs_mul, abs_mul, abs_pow]
      simp only [abs_neg, abs_one, one_pow, one_mul]
      rw [abs_of_nonneg (by exact_mod_cast binary_nonneg A hA i j)]

/-- Arbitrary low-degree cofactor peeling, under its precise scalar logarithmic margin. -/
theorem row_peel_strict {n : ℕ} (r : ℝ) (hs : 0 ≤ slope r)
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℤ) (hA : Binary A) (i : Fin (n+1))
    (hi : 0 < rowDegree A i)
    (hmargin : log (rowDegree A i:ℝ) + slope r*(r-(rowDegree A i:ℝ)) < rate r)
    (hsmall : ∀ B : Matrix (Fin n) (Fin n) ℤ, Binary B →
      |(B.det:ℝ)| ≤ exp (exponent r n (edgeCount B))) :
    |(A.det:ℝ)| < exp (exponent r (n+1) (edgeCount A)) := by
  let k : ℝ := rowDegree A i
  let E : ℝ := (n:ℝ)*rate r + slope r*((edgeCount A:ℝ)-k-r*(n:ℝ))
  have hkp : 0 < k := by
    dsimp [k]
    exact_mod_cast hi
  have hm (j : Fin (n+1)) : |((laplaceMinor A i j).det:ℝ)| ≤ exp E := by
    apply (hsmall _ (laplaceMinor_binary A hA i j)).trans
    apply exp_le_exp.mpr
    have he : (edgeCount (laplaceMinor A i j):ℝ) ≤ (edgeCount A:ℝ)-k := by
      dsimp [k]
      exact_mod_cast minor_edgeCount_le A hA i j
    have ht := mul_le_mul_of_nonneg_left (sub_le_sub_right he (r*(n:ℝ))) hs
    dsimp [exponent, E]
    linarith
  have hb : |(A.det:ℝ)| ≤ k*exp E := by
    apply (abs_det_le_cofactors A hA i).trans
    calc
      (∑ j, (A i j:ℝ)*|((laplaceMinor A i j).det:ℝ)|) ≤
          ∑ j, (A i j:ℝ)*exp E :=
        sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hm j)
          (by exact_mod_cast binary_nonneg A hA i j)
      _ = k*exp E := by rw [← sum_mul]; simp [k, rowDegree]
  apply hb.trans_lt
  rw [← exp_log hkp, ← exp_add]
  apply exp_lt_exp.mpr
  dsimp [exponent, E, k]
  push_cast
  linarith

theorem column_peel_strict {n : ℕ} (r : ℝ) (hs : 0 ≤ slope r)
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℤ) (hA : Binary A) (j : Fin (n+1))
    (hj : 0 < columnDegree A j)
    (hmargin : log (columnDegree A j:ℝ) + slope r*(r-(columnDegree A j:ℝ)) < rate r)
    (hsmall : ∀ B : Matrix (Fin n) (Fin n) ℤ, Binary B →
      |(B.det:ℝ)| ≤ exp (exponent r n (edgeCount B))) :
    |(A.det:ℝ)| < exp (exponent r (n+1) (edgeCount A)) := by
  simpa only [Matrix.det_transpose, edgeCount_transpose] using
    row_peel_strict r hs A.transpose (binary_transpose A hA) j hj hmargin hsmall

/-- A complete scalar certificate interface for any density, with all matrix steps discharged. -/
theorem determinant_from_certificate (r : ℝ) (hr : 2 < r) (K : ℤ) (hK : 0 ≤ K)
    (anchor : ℝ → ℝ) (hcert : EdgeCertificate r K anchor)
    (hpeel : ∀ k : ℤ, 0 < k → k ≤ K → log (k:ℝ)+slope r*(r-(k:ℝ)) < rate r)
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) (hA : Binary A) :
    |(A.det:ℝ)| ≤ exp (exponent r n (edgeCount A)) := by
  induction n with
  | zero => simp [exponent, edgeCount]
  | succ n ih =>
    by_cases hdet : A.det = 0
    · simpa only [hdet, Int.cast_zero, abs_zero] using (exp_pos (exponent r (n+1) (edgeCount A))).le
    by_cases hd : ∀ i, K < rowDegree A i
    · by_cases hc : ∀ j, K < columnDegree A j
      · simpa only [Fintype.card_fin, exponent] using
          certificate_minimum_degree_bound r hr.le K hK anchor hcert A hA hdet hd hc
      · obtain ⟨j, hj⟩ := not_forall.mp hc
        have hp := columnDegree_pos_of_det_ne_zero A hA hdet j
        exact (column_peel_strict r (slope_pos r hr).le A hA j hp
          (hpeel _ hp (by omega)) ih).le
    · obtain ⟨i, hi⟩ := not_forall.mp hd
      have hp := rowDegree_pos_of_det_ne_zero A hA hdet i
      exact (row_peel_strict r (slope_pos r hr).le A hA i hp
        (hpeel _ hp (by omega)) ih).le

/-- Total-count corollary. The two scalar certificate hypotheses remain explicit. -/
theorem determinant_total_count_from_certificate (r : ℝ) (hr : 2 < r) (K : ℤ) (hK : 0 ≤ K)
    (anchor : ℝ → ℝ) (hcert : EdgeCertificate r K anchor)
    (hpeel : ∀ k : ℤ, 0 < k → k ≤ K → log (k:ℝ)+slope r*(r-(k:ℝ)) < rate r)
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) (hA : Binary A)
    (he : (edgeCount A:ℝ) ≤ r*(n:ℝ)) :
    |(A.det:ℝ)| ≤ exp ((n:ℝ)*rate r) := by
  apply (determinant_from_certificate r hr K hK anchor hcert hpeel n A hA).trans
  apply exp_le_exp.mpr
  unfold exponent
  have hm := mul_nonpos_of_nonneg_of_nonpos (slope_pos r hr).le (sub_nonpos.mpr he)
  linarith
end SparseComponent.TotalFamily
