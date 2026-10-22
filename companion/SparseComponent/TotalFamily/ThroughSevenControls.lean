import SparseComponent.TotalFamily.ThroughSeven

namespace SparseComponent.TotalFamily.ThroughSevenControls
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
theorem high_degree_control (r : ℕ) (hr0 : 3 ≤ r) (hr1 : r ≤ 7) :
    |(irregularFifteen.det:ℝ)| ≤ exp ((15:ℝ)*rate r) := by
  apply determinant_total_through_seven_budget r hr0 hr1 15 irregularFifteen irregularFifteen_binary
  rw [irregularFifteen_ones]
  have hr : (3:ℤ) ≤ r := by exact_mod_cast hr0
  norm_num
  omega

theorem irregularFifteen_transpose_degree : columnDegree irregularFifteen.transpose 0 = 15 := by decide

/-- The transpose exercises the endpoint on a genuinely unbounded column degree. -/
theorem high_column_control (r : ℕ) (hr0 : 3 ≤ r) (hr1 : r ≤ 7) :
    |(irregularFifteen.transpose.det:ℝ)| ≤ exp ((15:ℝ)*rate r) := by
  apply determinant_total_through_seven_budget r hr0 hr1 15 irregularFifteen.transpose
    (binary_transpose irregularFifteen irregularFifteen_binary)
  rw [edgeCount_transpose, irregularFifteen_ones]
  have hr : (3:ℤ) ≤ r := by exact_mod_cast hr0
  norm_num
  omega

/-- The empty matrix realizes the vacuous exact component classification at every density. -/
theorem empty_equality (r : ℕ) (hr0 : 3 ≤ r) (hr1 : r ≤ 7)
    (A : Matrix (Fin 0) (Fin 0) ℤ) (hA : Binary A) :
    |(A.det:ℝ)| = exp (exponent r 0 (edgeCount A)) := by
  apply (determinant_total_through_seven_equality_iff r hr0 hr1 0 A hA).mpr
  intro i
  exact Fin.elim0 i

/-- Singular binary matrices are admitted without positivity or spectral premises. -/
theorem singular_control (r : ℕ) (hr0 : 3 ≤ r) (hr1 : r ≤ 7) :
    |((0 : Matrix (Fin 3) (Fin 3) ℤ).det:ℝ)| ≤ exp ((3:ℝ)*rate r) := by
  apply determinant_total_through_seven_budget r hr0 hr1
  · intro i j; left; rfl
  · simp [edgeCount, rowDegree] <;> positivity
end SparseComponent.TotalFamily.ThroughSevenControls
