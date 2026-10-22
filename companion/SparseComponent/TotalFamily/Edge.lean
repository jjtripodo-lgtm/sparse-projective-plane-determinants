import SparseComponent.TotalFamily.Vertex

namespace SparseComponent.TotalFamily
open Finset Matrix Real TotalOnes
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

noncomputable def edgeForward (r : ℝ) (anchor : ℝ → ℝ) (d c : ℝ) : ℝ :=
  (deficit r d (anchor (1/d)) + deficitDerivative r d (anchor (1/d))*(1/c-anchor (1/d)))/d
noncomputable def edgeCost (r : ℝ) (anchor : ℝ → ℝ) (d c : ℝ) : ℝ :=
  edgeForward r anchor d c + edgeForward r anchor c d

/-- The analytic certificate is a scalar two-integer condition, not a matrix-bound assumption. -/
def EdgeCertificate (r : ℝ) (K : ℤ) (anchor : ℝ → ℝ) : Prop :=
  ∀ d c : ℤ, K < d → K < c → 0 ≤ edgeCost r anchor d c

def StrictEdgeCertificate (r : ℝ) (K : ℤ) (anchor : ℝ → ℝ) : Prop :=
  EdgeCertificate r K anchor ∧ ∀ d c : ℤ, K < d → K < c →
    edgeCost r anchor d c = 0 → (d:ℝ) = r ∧ (c:ℝ) = r

theorem edgeCost_symm (r : ℝ) (anchor : ℝ → ℝ) (d c : ℝ) :
    edgeCost r anchor d c = edgeCost r anchor c d := by
  unfold edgeCost
  ring

theorem edgeCost_plane (r : ℝ) (hr : r ≠ 0) (anchor : ℝ → ℝ)
    (ha : anchor (1/r) = 1/r) : edgeCost r anchor r r = 0 := by
  simp only [edgeCost, edgeForward, ha, deficit_plane r hr, deficitDerivative_plane r hr,
    zero_mul, zero_add, zero_div]

/-- Incidence averaging turns each supporting tangent into a sum over actual edges. -/
theorem tangent_sum_identity (r d : ℝ) (hd : d ≠ 0) (anchor : ℝ → ℝ)
    (w c : ι → ℝ) (hw : ∑ j, w j = d) :
    (∑ j, w j * edgeForward r anchor d (c j)) =
      deficit r d (anchor (1/d)) + deficitDerivative r d (anchor (1/d))*
        ((∑ j, w j/(d*c j))-anchor (1/d)) := by
  have he (j : ι) : w j * edgeForward r anchor d (c j) =
      (w j/d)*deficit r d (anchor (1/d)) + deficitDerivative r d (anchor (1/d))*
        (w j/(d*c j)-(w j/d)*anchor (1/d)) := by
    unfold edgeForward
    simp only [div_eq_mul_inv, _root_.mul_inv_rev]
    ring
  simp_rw [he]
  simp only [sum_add_distrib, sum_sub_distrib, ← sum_mul, ← mul_sum, ← sum_div, hw, div_self hd]
  ring

theorem row_tangent_bound (r : ℝ) (hr : 2 ≤ r) (anchor : ℝ → ℝ)
    (A : Matrix ι ι ℤ) (hd : ∀ i, 0 < rowDegree A i) (i : ι) :
    (∑ j, (A i j:ℝ)*edgeForward r anchor (rowSize A i) (columnSize A j)) ≤
      deficit r (rowSize A i) (rowMass A i) := by
  rw [tangent_sum_identity r _ (rowSize_pos A hd i).ne' anchor _ _
    (by simp [rowSize, rowDegree])]
  exact deficit_tangent_le r hr _ _ _

theorem column_tangent_bound (r : ℝ) (hr : 2 ≤ r) (anchor : ℝ → ℝ)
    (A : Matrix ι ι ℤ) (hc : ∀ j, 0 < columnDegree A j) (j : ι) :
    (∑ i, (A i j:ℝ)*edgeForward r anchor (columnSize A j) (rowSize A i)) ≤
      deficit r (columnSize A j) (columnMass A j) := by
  rw [tangent_sum_identity r _ (columnSize_pos A hc j).ne' anchor _ _
    (by simp [columnSize, columnDegree])]
  have he : (∑ i, (A i j:ℝ)/(columnSize A j*rowSize A i)) = columnMass A j := by
    simp only [columnMass, mul_comm]
  rw [he]
  exact deficit_tangent_le r hr _ _ _

theorem edge_sum_le_deficit (r : ℝ) (hr : 2 ≤ r) (anchor : ℝ → ℝ)
    (A : Matrix ι ι ℤ) (hd : ∀ i, 0 < rowDegree A i) (hc : ∀ j, 0 < columnDegree A j) :
    (∑ i, ∑ j, (A i j:ℝ)*edgeCost r anchor (rowSize A i) (columnSize A j)) ≤
      (∑ i, deficit r (rowSize A i) (rowMass A i)) +
      (∑ j, deficit r (columnSize A j) (columnMass A j)) := by
  have hrb := sum_le_sum (s := (univ : Finset ι)) fun i _ => row_tangent_bound r hr anchor A hd i
  have hcb := sum_le_sum (s := (univ : Finset ι)) fun j _ => column_tangent_bound r hr anchor A hc j
  have he : (∑ i, ∑ j, (A i j:ℝ)*edgeCost r anchor (rowSize A i) (columnSize A j)) =
      (∑ i, ∑ j, (A i j:ℝ)*edgeForward r anchor (rowSize A i) (columnSize A j)) +
      (∑ j, ∑ i, (A i j:ℝ)*edgeForward r anchor (columnSize A j) (rowSize A i)) := by
    simp only [edgeCost, mul_add, sum_add_distrib]
    rw [sum_comm (f := fun i j => (A i j:ℝ)*edgeForward r anchor (columnSize A j) (rowSize A i))]
  rw [he]
  linarith

/-- The universal matrix-to-edge inequality. No scalar certificate is needed for this step. -/
theorem matrix_log_edge_bound (r : ℝ) (hr : 2 ≤ r) (anchor : ℝ → ℝ)
    (A : Matrix ι ι ℤ) (hA : Binary A) (hdet : A.det ≠ 0)
    (hd : ∀ i, 0 < rowDegree A i) (hc : ∀ j, 0 < columnDegree A j) :
    log |(A.det:ℝ)| ≤ (Fintype.card ι:ℝ)*rate r + slope r*((edgeCount A:ℝ)-r*(Fintype.card ι:ℝ)) -
      (∑ i, ∑ j, (A i j:ℝ)*edgeCost r anchor (rowSize A i) (columnSize A j))/2 := by
  have hs := matrix_log_deficit r hr A hA hdet hd hc
  have he := edge_sum_le_deficit r hr anchor A hd hc
  linarith

theorem certificate_minimum_degree_bound (r : ℝ) (hr : 2 ≤ r) (K : ℤ) (hK : 0 ≤ K)
    (anchor : ℝ → ℝ) (hcert : EdgeCertificate r K anchor)
    (A : Matrix ι ι ℤ) (hA : Binary A) (hdet : A.det ≠ 0)
    (hd : ∀ i, K < rowDegree A i) (hc : ∀ j, K < columnDegree A j) :
    |(A.det:ℝ)| ≤ exp ((Fintype.card ι:ℝ)*rate r + slope r*((edgeCount A:ℝ)-r*(Fintype.card ι:ℝ))) := by
  have hdp (i : ι) : 0 < rowDegree A i := lt_of_le_of_lt hK (hd i)
  have hcp (j : ι) : 0 < columnDegree A j := lt_of_le_of_lt hK (hc j)
  have hs := matrix_log_edge_bound r hr anchor A hA hdet hdp hcp
  have he : 0 ≤ ∑ i, ∑ j, (A i j:ℝ)*edgeCost r anchor (rowSize A i) (columnSize A j) := by
    apply sum_nonneg
    intro i _
    apply sum_nonneg
    intro j _
    exact mul_nonneg (by exact_mod_cast binary_nonneg A hA i j)
      (hcert (rowDegree A i) (columnDegree A j) (hd i) (hc j))
  apply (log_le_iff_le_exp (abs_pos.mpr (by exact_mod_cast hdet))).mp
  linarith
end SparseComponent.TotalFamily
