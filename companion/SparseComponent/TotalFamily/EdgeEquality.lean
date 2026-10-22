import SparseComponent.TotalFamily.Peeling

namespace SparseComponent.TotalFamily
open Finset Matrix Real TotalOnes
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- A strict edge certificate forces actual row and column regularity at equality. -/
theorem certificate_minimum_degree_equality_regular (r : ℝ) (hr : 2 ≤ r)
    (K : ℤ) (hK : 0 ≤ K) (anchor : ℝ → ℝ) (hcert : StrictEdgeCertificate r K anchor)
    (A : Matrix ι ι ℤ) (hA : Binary A) (hdet : A.det ≠ 0)
    (hd : ∀ i, K < rowDegree A i) (hc : ∀ j, K < columnDegree A j)
    (heq : |(A.det:ℝ)| = exp ((Fintype.card ι:ℝ)*rate r+slope r*((edgeCount A:ℝ)-r*(Fintype.card ι:ℝ)))) :
    (∀ i, rowSize A i = r) ∧ (∀ j, columnSize A j = r) := by
  have hdp (i : ι) : 0 < rowDegree A i := lt_of_le_of_lt hK (hd i)
  have hcp (j : ι) : 0 < columnDegree A j := lt_of_le_of_lt hK (hc j)
  have hn (i j : ι) : 0 ≤ (A i j:ℝ)*edgeCost r anchor (rowSize A i) (columnSize A j) :=
    mul_nonneg (by exact_mod_cast binary_nonneg A hA i j)
      (hcert.1 _ _ (hd i) (hc j))
  have hs := matrix_log_edge_bound r hr anchor A hA hdet hdp hcp
  rw [heq, log_exp] at hs
  have hz : (∑ i, ∑ j, (A i j:ℝ)*edgeCost r anchor (rowSize A i) (columnSize A j)) = 0 := by
    have hn' : 0 ≤ ∑ i, ∑ j, (A i j:ℝ)*edgeCost r anchor (rowSize A i) (columnSize A j) :=
      sum_nonneg fun i _ => sum_nonneg fun j _ => hn i j
    linarith
  have he (i j : ι) (hij : A i j = 1) : rowSize A i = r ∧ columnSize A j = r := by
    have hi := (sum_eq_zero_iff_of_nonneg (fun i _ => sum_nonneg fun j _ => hn i j)).mp hz i (mem_univ i)
    have hj := (sum_eq_zero_iff_of_nonneg (fun j _ => hn i j)).mp hi j (mem_univ j)
    simp only [hij, Int.cast_one, one_mul] at hj
    exact hcert.2 _ _ (hd i) (hc j) hj
  constructor
  · intro i
    have hnz : (∑ j, A i j) ≠ 0 := (hdp i).ne'
    obtain ⟨j, _, hj⟩ := exists_ne_zero_of_sum_ne_zero hnz
    exact (he i j ((hA i j).resolve_left hj)).1
  · intro j
    have hnz : (∑ i, A i j) ≠ 0 := (hcp j).ne'
    obtain ⟨i, _, hi⟩ := exists_ne_zero_of_sum_ne_zero hnz
    exact (he i j ((hA i j).resolve_left hi)).2

/-- Full all-order regularity transfer, with only explicit scalar certificate gates. -/
theorem equality_regular_from_edge_certificate (r : ℝ) (hr : 2 < r) (K : ℤ) (hK : 0 ≤ K)
    (anchor : ℝ → ℝ) (hcert : StrictEdgeCertificate r K anchor)
    (hpeel : ∀ k : ℤ, 0 < k → k ≤ K → log (k:ℝ)+slope r*(r-(k:ℝ)) < rate r)
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) (hA : Binary A)
    (heq : |(A.det:ℝ)| = exp (exponent r n (edgeCount A))) :
    (∀ i, rowSize A i = r) ∧ (∀ j, columnSize A j = r) := by
  cases n with
  | zero => constructor <;> intro i <;> exact Fin.elim0 i
  | succ n =>
    have hdet : A.det ≠ 0 := by
      intro hz
      have hp := exp_pos (exponent r (n+1) (edgeCount A))
      simp only [hz, Int.cast_zero, abs_zero] at heq
      linarith
    have hsmall := determinant_from_certificate r hr K hK anchor hcert.1 hpeel n
    have hd : ∀ i, K < rowDegree A i := by
      intro i
      by_contra hn
      have hp := rowDegree_pos_of_det_ne_zero A hA hdet i
      have h := row_peel_strict r (slope_pos r hr).le A hA i hp (hpeel _ hp (by omega)) hsmall
      linarith
    have hc : ∀ j, K < columnDegree A j := by
      intro j
      by_contra hn
      have hp := columnDegree_pos_of_det_ne_zero A hA hdet j
      have h := column_peel_strict r (slope_pos r hr).le A hA j hp (hpeel _ hp (by omega)) hsmall
      linarith
    apply certificate_minimum_degree_equality_regular r hr.le K hK anchor hcert A hA hdet hd hc
    simpa only [Fintype.card_fin, exponent] using heq
end SparseComponent.TotalFamily
