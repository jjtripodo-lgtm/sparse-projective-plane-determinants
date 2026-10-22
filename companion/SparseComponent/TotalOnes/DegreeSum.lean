import SparseComponent.TotalOnes.DegreeMajorant

namespace SparseComponent.TotalOnes
open Finset
variable {ι : Type*} [Fintype ι]

/-- Exact affine sum before the matrix-weighted balance is substituted. -/
theorem sum_degree_affine (d : ι → ℤ) (u : ι → ℝ) :
    (∑ i, (baseDegreeValue + edgeSlope*((d i:ℝ)-3) + balanceSlope*((d i:ℝ)*u i-1))) =
      (Fintype.card ι:ℝ)*baseDegreeValue +
        edgeSlope*((∑ i, (d i:ℝ))-3*(Fintype.card ι:ℝ)) +
        balanceSlope*((∑ i, (d i:ℝ)*u i)-(Fintype.card ι:ℝ)) := by
  simp only [mul_sub, sum_add_distrib, sum_sub_distrib, sum_mul, mul_sum,
    sum_const, card_univ, nsmul_eq_mul]
  ring

/-- One side of the separable majorant, with the weighted balance explicit. -/
theorem sum_degree_majorant (d : ι → ℤ) (u : ι → ℝ)
    (hd : ∀ i, 2 ≤ d i) (hu : ∀ i, 0 ≤ u i)
    (balance : ∑ i, (d i:ℝ)*u i = (Fintype.card ι:ℝ)) :
    (∑ i, degreeTerm (d i) (u i)) ≤
      (Fintype.card ι:ℝ)*baseDegreeValue +
        edgeSlope*((∑ i, (d i:ℝ))-3*(Fintype.card ι:ℝ)) := by
  have h := sum_le_sum (s := (univ : Finset ι)) (fun i _ => degree_majorant_int (d i) (hd i) (u i) (hu i))
  rw [sum_degree_affine, balance, sub_self, mul_zero, add_zero] at h
  exact h

/-- Aggregate tightness forces the exact degree and mass at every row. -/
theorem sum_degree_majorant_eq_iff (d : ι → ℤ) (u : ι → ℝ)
    (hd : ∀ i, 2 ≤ d i) (hu : ∀ i, 0 ≤ u i)
    (balance : ∑ i, (d i:ℝ)*u i = (Fintype.card ι:ℝ)) :
    (∑ i, degreeTerm (d i) (u i)) =
      (Fintype.card ι:ℝ)*baseDegreeValue +
        edgeSlope*((∑ i, (d i:ℝ))-3*(Fintype.card ι:ℝ)) ↔
      ∀ i, d i = 3 ∧ u i = 1/3 := by
  have ha := sum_degree_affine d u
  rw [balance, sub_self, mul_zero, add_zero] at ha
  rw [← ha]
  rw [sum_eq_sum_iff_of_le (fun i (_ : i ∈ (univ : Finset ι)) =>
    degree_majorant_int (d i) (hd i) (u i) (hu i))]
  simp only [mem_univ, forall_const]
  exact forall_congr' (fun i => degree_majorant_int_eq_iff (d i) (hd i) (u i) (hu i))

end SparseComponent.TotalOnes
