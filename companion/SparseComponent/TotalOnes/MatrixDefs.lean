import SparseComponent.Gram
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.Real.Sqrt

/-!
Literal matrix data for the total-ones theorem. These definitions do not assume
degree caps, spectral bounds, regularity, or an analytic certificate.
-/

namespace SparseComponent.TotalOnes
open Finset Matrix
variable {ι : Type*} [Fintype ι]

def rowSize (A : Matrix ι ι ℤ) (i : ι) : ℝ := (rowDegree A i : ℝ)

def columnSize (A : Matrix ι ι ℤ) (j : ι) : ℝ := (columnDegree A j : ℝ)

def edgeCount (A : Matrix ι ι ℤ) : ℤ := ∑ i, rowDegree A i

noncomputable def rowMass (A : Matrix ι ι ℤ) (i : ι) : ℝ :=
  ∑ j, (A i j : ℝ) / (rowSize A i * columnSize A j)

noncomputable def columnMass (A : Matrix ι ι ℤ) (j : ι) : ℝ :=
  ∑ i, (A i j : ℝ) / (rowSize A i * columnSize A j)

noncomputable def normalizedMatrix (A : Matrix ι ι ℤ) : Matrix ι ι ℝ :=
  fun i j => (A i j : ℝ) / (Real.sqrt (rowSize A i) * Real.sqrt (columnSize A j))

noncomputable def normalizedGram (A : Matrix ι ι ℤ) : Matrix ι ι ℝ :=
  (9 : ℝ) • (normalizedMatrix A * (normalizedMatrix A).transpose)

end SparseComponent.TotalOnes
