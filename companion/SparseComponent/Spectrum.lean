import SparseComponent.Moments
import Mathlib.Analysis.Matrix.PosDef

namespace SparseComponent
open Finset Matrix
open scoped ComplexOrder
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

def realMatrix (A : Matrix ι ι ℤ) : Matrix ι ι ℝ := Matrix.of (fun i j => (A i j : ℝ))
def realGram (A : Matrix ι ι ℤ) : Matrix ι ι ℝ := Matrix.of (fun i j => (gram A i j : ℝ))

theorem realGram_eq (A : Matrix ι ι ℤ) : realGram A = realMatrix A * (realMatrix A).transpose := by
  ext i j
  simp [realGram, realMatrix, gram, Matrix.mul_apply]

theorem realGram_posSemidef (A : Matrix ι ι ℤ) : (realGram A).PosSemidef := by
  rw [realGram_eq, ← Matrix.conjTranspose_eq_transpose_of_trivial]
  exact Matrix.posSemidef_self_mul_conjTranspose _

theorem realMatrix_det (A : Matrix ι ι ℤ) : (realMatrix A).det = (A.det : ℝ) := by
  exact (RingHom.map_det (Int.castRingHom ℝ) A).symm

theorem realGram_det (A : Matrix ι ι ℤ) : (realGram A).det = (A.det : ℝ) ^ 2 := by
  rw [realGram_eq, Matrix.det_mul, Matrix.det_transpose, realMatrix_det]
  ring

/-- Elementary nonnegative row-sum bound for any real eigenvector. -/
theorem eigenvalue_le_row_cap (B : Matrix ι ι ℝ) (hn : ∀ i j, 0 ≤ B i j)
    (R : ℝ) (hc : ∀ i, ∑ j, B i j ≤ R)
    (w : ι → ℝ) (hw : w ≠ 0) (mu : ℝ) (he : B *ᵥ w = mu • w) : mu ≤ R := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hw
  have hj' : w j ≠ 0 := hj
  obtain ⟨k, hk, hmax⟩ := univ.exists_max_image (fun k => |w k|) ⟨j, mem_univ j⟩
  have hkpos : 0 < |w k| := (abs_pos.mpr hj').trans_le (hmax j (mem_univ j))
  have hkEq : (∑ j, B k j * w j) = mu * w k := congrFun he k
  have hb : |mu| * |w k| ≤ R * |w k| := by
    calc
      _ = |∑ j, B k j * w j| := by rw [hkEq, abs_mul]
      _ ≤ ∑ j, |B k j * w j| := abs_sum_le_sum_abs _ _
      _ = ∑ j, B k j * |w j| := by simp_rw [abs_mul, abs_of_nonneg (hn k _)]
      _ ≤ ∑ j, B k j * |w k| := sum_le_sum (fun j _ =>
        mul_le_mul_of_nonneg_left (hmax j (mem_univ j)) (hn k j))
      _ = (∑ j, B k j) * |w k| := (sum_mul ..).symm
      _ ≤ R * |w k| := mul_le_mul_of_nonneg_right (hc k) hkpos.le
  have : |mu| ≤ R := (mul_le_mul_iff_left₀ hkpos).mp (by nlinarith [hb])
  exact (le_abs_self mu).trans this

noncomputable def eigenvalues (A : Matrix ι ι ℤ) : ι → ℝ :=
  (realGram_posSemidef A).isHermitian.eigenvalues

theorem eigenvalues_nonneg (A : Matrix ι ι ℤ) (i : ι) : 0 ≤ eigenvalues A i :=
  (realGram_posSemidef A).eigenvalues_nonneg i

theorem eigenvalues_positive (A : Matrix ι ι ℤ) (hdet : A.det ≠ 0) (i : ι) :
    0 < eigenvalues A i := by
  have hp : (∏ j, eigenvalues A j) ≠ 0 := by
    have hprod := (realGram_posSemidef A).isHermitian.det_eq_prod_eigenvalues
    simp only [RCLike.ofReal_real_eq_id, id_eq] at hprod
    unfold eigenvalues
    rw [← hprod, realGram_det]
    exact pow_ne_zero 2 (by exact_mod_cast hdet)
  have hn : eigenvalues A i ≠ 0 := (prod_ne_zero_iff.mp hp) i (mem_univ i)
  exact lt_of_le_of_ne (eigenvalues_nonneg A i) (Ne.symm hn)

theorem eigenvalues_cap (A : Matrix ι ι ℤ) (hA : Binary A)
    (r : ℤ) (hr : 0 ≤ r) (hc : ∀ k, columnDegree A k ≤ r)
    (hd : ∀ i, rowDegree A i ≤ r) (i : ι) : eigenvalues A i ≤ (r : ℝ) ^ 2 := by
  let hG := (realGram_posSemidef A).isHermitian
  apply eigenvalue_le_row_cap (realGram A)
    (fun j k => by
      change (0 : ℝ) ≤ (gram A j k : ℝ)
      exact_mod_cast gram_nonneg A hA j k) ((r : ℝ) ^ 2)
    (fun j => by
      change (∑ k, (gram A j k : ℝ)) ≤ (r : ℝ) ^ 2
      have h := gram_rowSum_cap A hA r hr hc hd j
      unfold rowSum at h
      exact_mod_cast h)
    (hG.eigenvectorBasis i).ofLp
  · intro hw
    have hz : hG.eigenvectorBasis i = 0 := (WithLp.ofLp_eq_zero 2).mp hw
    exact hG.eigenvectorBasis.orthonormal.linearIndependent.ne_zero i hz
  · exact hG.mulVec_eigenvectorBasis i

theorem eigenvalues_sum (A : Matrix ι ι ℤ) (hA : Binary A) :
    (∑ i, eigenvalues A i) = ((∑ i, rowDegree A i) : ℤ) := by
  have hsum := (realGram_posSemidef A).isHermitian.trace_eq_sum_eigenvalues
  simp only [RCLike.ofReal_real_eq_id, id_eq] at hsum
  unfold eigenvalues
  rw [← hsum]
  simp [Matrix.trace, Matrix.diag, realGram, gram_diagonal A hA]

end SparseComponent
