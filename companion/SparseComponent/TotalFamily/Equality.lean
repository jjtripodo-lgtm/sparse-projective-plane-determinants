import SparseComponent.TotalFamily.Separable
import SparseComponent.Extremizers

namespace SparseComponent.TotalFamily
open Finset Matrix Real TotalOnes
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

theorem exp_rate_eq_design (r n : ℝ) (hr : 2 ≤ r) :
    exp (n*rate r) = designBlockDet r^(n/planeOrder r) := by
  rw [rpow_def_of_pos (designBlockDet_positive r hr)]
  have h := designBlockDet_log r hr
  change log (designBlockDet r)/planeOrder r = rate r at h
  rw [← h]
  congr 1
  ring

/-- Equality in the separable matrix bound forces the degree supplied by the strict scalar gate. -/
theorem minimum_degree_equality_regular (r : ℝ) (hr : 2 ≤ r)
    (hcert : ∀ d : ℤ, 2 ≤ d → ∀ u : ℝ, 0 ≤ u → 0 ≤ deficit r d u)
    (hstrict : ∀ d : ℤ, 2 ≤ d → ∀ u : ℝ, 0 ≤ u → deficit r d u = 0 → (d:ℝ) = r)
    (A : Matrix ι ι ℤ) (hA : Binary A) (hdet : A.det ≠ 0)
    (hd : ∀ i, 2 ≤ rowDegree A i) (hc : ∀ j, 2 ≤ columnDegree A j)
    (heq : |(A.det:ℝ)| = exp ((Fintype.card ι:ℝ)*rate r+slope r*((edgeCount A:ℝ)-r*(Fintype.card ι:ℝ)))) :
    (∀ i, rowSize A i = r) ∧ (∀ j, columnSize A j = r) := by
  have hdp (i : ι) : 0 < rowDegree A i := by linarith [hd i]
  have hcp (j : ι) : 0 < columnDegree A j := by linarith [hc j]
  have hs := matrix_log_deficit r hr A hA hdet hdp hcp
  have hrow (i : ι) : 0 ≤ deficit r (rowSize A i) (rowMass A i) :=
    hcert _ (hd i) _ (rowMass_nonneg A hA hdp hcp i)
  have hcol (j : ι) : 0 ≤ deficit r (columnSize A j) (columnMass A j) :=
    hcert _ (hc j) _ (columnMass_nonneg A hA hdp hcp j)
  have hsr := sum_nonneg (s := (univ : Finset ι)) fun i _ => hrow i
  have hsc := sum_nonneg (s := (univ : Finset ι)) fun j _ => hcol j
  rw [heq, log_exp] at hs
  have hzr : (∑ i, deficit r (rowSize A i) (rowMass A i)) = 0 := by linarith
  have hzc : (∑ j, deficit r (columnSize A j) (columnMass A j)) = 0 := by linarith
  constructor
  · intro i
    exact hstrict _ (hd i) _ (rowMass_nonneg A hA hdp hcp i)
      ((sum_eq_zero_iff_of_nonneg (fun i _ => hrow i)).mp hzr i (mem_univ i))
  · intro j
    exact hstrict _ (hc j) _ (columnMass_nonneg A hA hdp hcp j)
      ((sum_eq_zero_iff_of_nonneg (fun j _ => hcol j)).mp hzc j (mem_univ j))

/-- Strict peeling excludes every low-degree equality case, including columns. -/
theorem equality_regular_from_vertex_certificate (r : ℝ) (hr : 2 < r)
    (hcert : ∀ d : ℤ, 2 ≤ d → ∀ u : ℝ, 0 ≤ u → 0 ≤ deficit r d u)
    (hstrict : ∀ d : ℤ, 2 ≤ d → ∀ u : ℝ, 0 ≤ u → deficit r d u = 0 → (d:ℝ) = r)
    (hpeel : slope r*(r-1) < rate r)
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
    have hsmall := determinant_from_vertex_certificate r hr hcert hpeel n
    have hd : ∀ i, 2 ≤ rowDegree A i := by
      intro i
      by_contra hn
      have hp := rowDegree_pos_of_det_ne_zero A hA hdet i
      have hk : rowDegree A i = 1 := by omega
      have h := row_peel_strict r (slope_pos r hr).le A hA i hp
        (by simpa [hk] using hpeel) hsmall
      linarith
    have hc : ∀ j, 2 ≤ columnDegree A j := by
      intro j
      by_contra hn
      have hp := columnDegree_pos_of_det_ne_zero A hA hdet j
      have hk : columnDegree A j = 1 := by omega
      have h := column_peel_strict r (slope_pos r hr).le A hA j hp
        (by simpa [hk] using hpeel) hsmall
      linarith
    apply minimum_degree_equality_regular r hr.le hcert hstrict A hA hdet hd hc
    simpa only [Fintype.card_fin, exponent] using heq

/-- The complete equality classification from strict scalar vertex and peeling certificates. -/
theorem equality_iff_all_plane_from_vertex_certificate (r : ℕ) (hr : 2 < r)
    (hcert : ∀ d : ℤ, 2 ≤ d → ∀ u : ℝ, 0 ≤ u → 0 ≤ deficit r d u)
    (hstrict : ∀ d : ℤ, 2 ≤ d → ∀ u : ℝ, 0 ≤ u → deficit r d u = 0 → (d:ℝ) = r)
    (hpeel : slope r*(r-1) < rate r)
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) (hA : Binary A) :
    |(A.det:ℝ)| = exp (exponent r n (edgeCount A)) ↔
      ∀ i, PlaneRows A r (component A i) := by
  have hrR : (2:ℝ) < r := by exact_mod_cast hr
  constructor
  · intro heq
    obtain ⟨hd,hc⟩ := equality_regular_from_vertex_certificate r hrR hcert hstrict hpeel n A hA heq
    have hdI (i) : rowDegree A i = r := by
      have hh : (rowDegree A i:ℝ) = r := hd i
      exact_mod_cast hh
    have hcI (j) : columnDegree A j = r := by
      have hh : (columnDegree A j:ℝ) = r := hc j
      exact_mod_cast hh
    have hedge : edgeCount A = (r:ℤ)*(n:ℤ) := by simp [edgeCount, hdI]; ring
    have he : |(A.det:ℝ)| = exp ((n:ℝ)*rate r) := by
      simpa [exponent, hedge] using heq
    rw [exp_rate_eq_design r n hrR.le] at he
    exact (determinant_attains_iff_all_plane A hA r hr.le (fun j => (hcI j).le)
      (fun i => (hdI i).le)).mp (by simpa only [Fintype.card_fin] using he)
  · intro hp
    have hd := all_plane_rowDegree A hA (r:ℤ) hp
    have hc := all_plane_columnDegree_unconditional A hA (r:ℤ) hp
    have he := all_plane_determinant_eq A hA r hr.le (fun j => (hc j).le) (fun i => (hd i).le) hp
    have hedge : edgeCount A = (r:ℤ)*(n:ℤ) := by simp [edgeCount, hd]; ring
    rw [exponent, hedge]
    simp only [Int.cast_mul, Int.cast_natCast, sub_self, mul_zero, add_zero]
    rw [exp_rate_eq_design r n hrR.le]
    simpa only [Fintype.card_fin] using he
end SparseComponent.TotalFamily
