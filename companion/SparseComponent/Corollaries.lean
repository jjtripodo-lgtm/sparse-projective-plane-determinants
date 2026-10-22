import SparseComponent.GlobalExtraction

namespace SparseComponent
open Finset Matrix Real
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

theorem residualRows_eq_card_of_no_plane (A : Matrix ι ι ℤ) (r : ℤ)
    (hp : ∀ i, ¬ PlaneRows A r (component A i)) :
    residualRows A r = Fintype.card ι := by
  simp [residualRows, badRows, hp]

/-- An actual plane-free support has an all-size exponential gap. -/
theorem plane_free_exponential_gap (A : Matrix ι ι ℤ) (hA : Binary A)
    (r : ℕ) (hr : 2 ≤ r) (hc : ∀ k, columnDegree A k ≤ r)
    (hd : ∀ i, rowDegree A i ≤ r)
    (hp : ∀ i, ¬ PlaneRows A r (component A i)) :
    |(A.det : ℝ)| ≤ exp ((Fintype.card ι : ℝ) * (blockLogRate r - stabilityCoefficient r)) := by
  have h := determinant_component_stability_exp A hA r hr hc hd
  rw [residualRows_eq_card_of_no_plane A r hp] at h
  convert h using 1
  push_cast
  congr 1
  ring

/-- The connected nonplane version needs no separate nonsingularity assumption. -/
theorem connected_nonplane_exponential_gap (A : Matrix ι ι ℤ) (hA : Binary A)
    (r : ℕ) (hr : 2 ≤ r) (hc : ∀ k, columnDegree A k ≤ r)
    (hd : ∀ i, rowDegree A i ≤ r) (i : ι)
    (hconn : ∀ j, Connected (gram A) i j) (hnp : ¬ PlaneRows A r (component A i)) :
    |(A.det : ℝ)| ≤ exp ((Fintype.card ι : ℝ) * (blockLogRate r - stabilityCoefficient r)) := by
  apply plane_free_exponential_gap A hA r hr hc hd
  intro j hp
  have hcomp := component_eq_of_mem A ((mem_component A i j).mpr (hconn j))
  exact hnp (hcomp ▸ hp)

theorem designBlockDet_three : designBlockDet (3 : ℝ) = 24 := by
  norm_num [designBlockDet, planeOrder, ← Real.rpow_natCast]

/-- The exact Fano-parameter specialization, with coefficient 1/4374. -/
theorem degree_three_component_stability (A : Matrix ι ι ℤ) (hA : Binary A)
    (hc : ∀ k, columnDegree A k ≤ 3) (hd : ∀ i, rowDegree A i ≤ 3) :
    |(A.det : ℝ)| ≤ (24 : ℝ) ^ ((Fintype.card ι : ℝ) / 7) *
      exp (-(residualRows A 3 : ℝ) / 4374) := by
  have h := determinant_component_stability A hA 3 (by norm_num) hc hd
  norm_num only [Nat.cast_ofNat, designBlockDet_three, planeOrder] at h
  norm_num at h ⊢
  exact h

/-- Near extremality forces the actual residual count down by the stated factor. -/
theorem near_extremal_residual_count (A : Matrix ι ι ℤ) (hA : Binary A)
    (r : ℕ) (hr : 2 ≤ r) (hc : ∀ k, columnDegree A k ≤ r)
    (hd : ∀ i, rowDegree A i ≤ r) (ε : ℝ)
    (hnear : exp ((Fintype.card ι : ℝ) * blockLogRate r - ε * Fintype.card ι) ≤ |(A.det : ℝ)|) :
    (residualRows A r : ℝ) ≤ 6 * (r : ℝ) ^ 6 * ε * Fintype.card ι := by
  have hu := determinant_component_stability_exp A hA r hr hc hd
  have h := exp_le_exp.mp (hnear.trans hu)
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hp : (0 : ℝ) < 6 * (r : ℝ) ^ 6 := by positivity
  have hn : (residualRows A r : ℝ) / (6 * (r : ℝ) ^ 6) ≤ ε * Fintype.card ι := by
    unfold stabilityCoefficient at h
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using (show
      1 / (6 * (r : ℝ) ^ 6) * (residualRows A r : ℝ) ≤ ε * Fintype.card ι by linarith)
  have hc' := (div_le_iff₀ hp).mp hn
  nlinarith

/-- The retained rows already belong to exact isolated plane blocks; no entries are edited. -/
theorem near_extremal_retained_rows (A : Matrix ι ι ℤ) (hA : Binary A)
    (r : ℕ) (hr : 2 ≤ r) (hc : ∀ k, columnDegree A k ≤ r)
    (hd : ∀ i, rowDegree A i ≤ r) (ε : ℝ)
    (hnear : exp ((Fintype.card ι : ℝ) * blockLogRate r - ε * Fintype.card ι) ≤ |(A.det : ℝ)|) :
    (1 - 6 * (r : ℝ) ^ 6 * ε) * Fintype.card ι ≤ (goodRows A r).card := by
  have hn := near_extremal_residual_count A hA r hr hc hd ε hnear
  have hcard : (residualRows A r : ℝ) + ((goodRows A r).card : ℝ) = Fintype.card ι := by
    unfold residualRows
    rw [badRows_eq_compl_goodRows]
    exact_mod_cast card_sdiff_add_card_eq_card (subset_univ (goodRows A r))
  nlinarith

end SparseComponent
