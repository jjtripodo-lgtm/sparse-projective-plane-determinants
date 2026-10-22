import SparseComponent.TotalFamily.FullFamily

namespace SparseComponent.TotalFamily.FullControls
open Finset Matrix Real TotalOnes

def irregularFifteen : Matrix (Fin 15) (Fin 15) ℤ := fun i j => if i=0 ∨ i=j then 1 else 0

theorem irregularFifteen_binary : Binary irregularFifteen := by
  intro i j
  by_cases h : i=0 ∨ i=j
  · right; simp [irregularFifteen, h]
  · left; simp [irregularFifteen, h]

theorem irregularFifteen_degree : rowDegree irregularFifteen 0 = 15 := by decide
theorem irregularFifteen_ones : edgeCount irregularFifteen = 29 := by decide

theorem irregularFifteen_det : irregularFifteen.det = 1 := by
  have ht : irregularFifteen.BlockTriangular id := by
    intro i j hij
    have hi : i ≠ 0 := by intro he; subst i; simp at hij
    have hne : i ≠ j := by simpa using (ne_of_gt hij)
    simp [irregularFifteen, hi, hne]
  rw [Matrix.det_of_upperTriangular ht]
  simp [irregularFifteen]

/-- The same nonsingular matrix exceeds every family's row cap while satisfying every total budget. -/
theorem high_degree_control (r : ℕ) (hr0 : 3 ≤ r) (hr1 : r ≤ 14) :
    |(irregularFifteen.det:ℝ)| ≤ exp ((15:ℝ)*rate r) := by
  apply determinant_total_family_budget r hr0 hr1 15 irregularFifteen irregularFifteen_binary
  rw [irregularFifteen_ones]
  have hr : (3:ℤ) ≤ r := by exact_mod_cast hr0
  norm_num
  omega

theorem irregularFifteen_transpose_degree : columnDegree irregularFifteen.transpose 0 = 15 := by decide

/-- The transpose exercises the endpoint on a genuinely unbounded column degree. -/
theorem high_column_control (r : ℕ) (hr0 : 3 ≤ r) (hr1 : r ≤ 14) :
    |(irregularFifteen.transpose.det:ℝ)| ≤ exp ((15:ℝ)*rate r) := by
  apply determinant_total_family_budget r hr0 hr1 15 irregularFifteen.transpose
    (binary_transpose irregularFifteen irregularFifteen_binary)
  rw [edgeCount_transpose, irregularFifteen_ones]
  have hr : (3:ℤ) ≤ r := by exact_mod_cast hr0
  norm_num
  omega

/-- The empty matrix realizes the vacuous exact component classification at every density. -/
theorem empty_equality (r : ℕ) (hr0 : 3 ≤ r) (hr1 : r ≤ 14)
    (A : Matrix (Fin 0) (Fin 0) ℤ) (hA : Binary A) :
    |(A.det:ℝ)| = exp (exponent r 0 (edgeCount A)) := by
  apply (determinant_total_family_equality_iff r hr0 hr1 0 A hA).mpr
  intro i
  exact Fin.elim0 i

/-- Singular binary matrices are admitted without positivity or spectral premises. -/
theorem singular_control (r : ℕ) (hr0 : 3 ≤ r) (hr1 : r ≤ 14) :
    |((0 : Matrix (Fin 3) (Fin 3) ℤ).det:ℝ)| ≤ exp ((3:ℝ)*rate r) := by
  apply determinant_total_family_budget r hr0 hr1
  · intro i j; left; rfl
  · simp [edgeCount, rowDegree] <;> positivity
/-- A dense nonsingular control exercises the normalized spectral branch: every degree is 16. -/
def denseSeventeen : Matrix (Fin 17) (Fin 17) ℤ := fun i j => if i=j then 0 else 1

def denseSeventeenPartner : Matrix (Fin 17) (Fin 17) ℤ := fun i j => if i=j then -15 else 1

theorem denseSeventeen_binary : Binary denseSeventeen := by
  intro i j
  by_cases h : i=j
  · left; simp [denseSeventeen, h]
  · right; simp [denseSeventeen, h]

theorem denseSeventeen_degrees : ∀ i, rowDegree denseSeventeen i = 16 ∧ columnDegree denseSeventeen i = 16 := by
  decide +kernel

theorem denseSeventeen_product : denseSeventeen*denseSeventeenPartner = (16:ℤ) • (1:Matrix (Fin 17) (Fin 17) ℤ) := by
  have h : ∀ i j : Fin 17, (denseSeventeen*denseSeventeenPartner) i j =
      ((16:ℤ) • (1:Matrix (Fin 17) (Fin 17) ℤ)) i j := by decide +kernel
  exact Matrix.ext h

theorem denseSeventeen_nonsingular : denseSeventeen.det ≠ 0 := by
  have h : denseSeventeen.det*denseSeventeenPartner.det = (16:ℤ)^17 := by
    rw [← Matrix.det_mul, denseSeventeen_product, Matrix.det_smul]
    norm_num
  intro hz
  rw [hz] at h
  norm_num at h

/-- The raw Gram matrix has all-ones eigenvalue 256, above every original r² cap in this family. -/
theorem denseSeventeen_raw_gram : ∀ i : Fin 17, (∑ j, SparseComponent.gram denseSeventeen i j) = 256 := by
  decide +kernel

theorem denseSeventeen_above_cap (r : ℕ) (hr : r ≤ 14) : (r:ℤ)^2 < 256 := by
  have hl : (0:ℤ) ≤ r := by positivity
  have hu : (r:ℤ) ≤ 14 := by exact_mod_cast hr
  have hs := mul_le_mul hu hu hl (by norm_num : (0:ℤ) ≤ 14)
  nlinarith only [hs]

theorem denseSeventeen_all_count (r : ℕ) (hr0 : 3 ≤ r) (hr1 : r ≤ 14) :
    |(denseSeventeen.det:ℝ)| ≤ exp (exponent r 17 (edgeCount denseSeventeen)) :=
  determinant_total_family r hr0 hr1 17 denseSeventeen denseSeventeen_binary

end SparseComponent.TotalFamily.FullControls
