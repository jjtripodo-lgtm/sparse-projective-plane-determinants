import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace SparseComponent
open Finset
variable {ι : Type*} [Fintype ι]

def rowSum (B : ι → ι → ℤ) (i : ι) : ℤ := ∑ j, B i j

def energy (B : ι → ι → ℤ) (R : ℤ) (w : ι → ℤ) : ℤ :=
  ∑ i, w i * (R * w i - ∑ j, B i j * w j)

/-- An integral version of the weighted Dirichlet identity. -/
theorem twice_energy (B : ι → ι → ℤ) (hB : ∀ i j, B i j = B j i)
    (R : ℤ) (w : ι → ℤ) :
    2 * energy B R w =
      2 * (∑ i, (R - rowSum B i) * w i ^ 2) +
      ∑ i, ∑ j, B i j * (w i - w j) ^ 2 := by
  have swap : (∑ i, ∑ j, B i j * w j ^ 2) =
      ∑ i, ∑ j, B i j * w i ^ 2 := by
    rw [sum_comm]
    apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro j hj
    rw [hB j i]
  have edge : (∑ i, ∑ j, B i j * (w i - w j) ^ 2) =
      2 * (∑ i, ∑ j, B i j * w i ^ 2) -
      2 * (∑ i, ∑ j, w i * (B i j * w j)) := by
    simp_rw [show ∀ i j, B i j * (w i - w j) ^ 2 =
      B i j * w i ^ 2 + B i j * w j ^ 2 - 2 * (w i * (B i j * w j)) by
        intros; ring]
    simp only [sum_sub_distrib, sum_add_distrib, ← mul_sum]
    rw [swap]
    ring
  rw [edge]
  simp only [energy, rowSum, mul_sub, sub_mul, sum_sub_distrib,
    mul_sum, sum_mul]
  have h : (∑ i, w i * (R * w i)) = ∑ i, R * w i ^ 2 := by
    apply sum_congr rfl
    intro i hi
    ring
  simp only [← mul_sum]
  rw [h]
  simp only [← mul_sum]
  ring

theorem energy_nonneg (B : ι → ι → ℤ) (hB : ∀ i j, B i j = B j i)
    (hn : ∀ i j, 0 ≤ B i j) (R : ℤ) (hc : ∀ i, rowSum B i ≤ R)
    (w : ι → ℤ) : 0 ≤ energy B R w := by
  have hd : 0 ≤ ∑ i, (R - rowSum B i) * w i ^ 2 :=
    sum_nonneg fun i _ => mul_nonneg (sub_nonneg.mpr (hc i)) (sq_nonneg _)
  have he : 0 ≤ ∑ i, ∑ j, B i j * (w i - w j) ^ 2 :=
    sum_nonneg fun i _ => sum_nonneg fun j _ => mul_nonneg (hn i j) (sq_nonneg _)
  have := twice_energy B hB R w
  omega

/-- Zero energy forces both vanishing degree slack and equality across every positive edge. -/
theorem energy_eq_zero_rigidity (B : ι → ι → ℤ) (hB : ∀ i j, B i j = B j i)
    (hn : ∀ i j, 0 ≤ B i j) (R : ℤ) (hc : ∀ i, rowSum B i ≤ R)
    (w : ι → ℤ) (hz : energy B R w = 0) :
    (∀ i, w i ≠ 0 → rowSum B i = R) ∧
    (∀ i j, B i j ≠ 0 → w i = w j) := by
  have hd : 0 ≤ ∑ i, (R - rowSum B i) * w i ^ 2 :=
    sum_nonneg fun i _ => mul_nonneg (sub_nonneg.mpr (hc i)) (sq_nonneg _)
  have he : 0 ≤ ∑ i, ∑ j, B i j * (w i - w j) ^ 2 :=
    sum_nonneg fun i _ => sum_nonneg fun j _ => mul_nonneg (hn i j) (sq_nonneg _)
  have hid := twice_energy B hB R w
  rw [hz] at hid
  have hd0 : (∑ i, (R - rowSum B i) * w i ^ 2) = 0 := by omega
  have he0 : (∑ i, ∑ j, B i j * (w i - w j) ^ 2) = 0 := by omega
  constructor
  · intro i hi
    have hi0 := (sum_eq_zero_iff_of_nonneg
      (fun i _ => mul_nonneg (sub_nonneg.mpr (hc i)) (sq_nonneg (w i)))).mp hd0 i (mem_univ i)
    have := (mul_eq_zero.mp hi0).resolve_right (pow_ne_zero 2 hi)
    omega
  · intro i j hij
    have hi0 := (sum_eq_zero_iff_of_nonneg
      (fun i _ => sum_nonneg fun j _ => mul_nonneg (hn i j) (sq_nonneg (w i - w j)))).mp he0 i (mem_univ i)
    have hj0 := (sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_nonneg (hn i j) (sq_nonneg (w i - w j)))).mp hi0 j (mem_univ j)
    have hsq := (mul_eq_zero.mp hj0).resolve_left hij
    have : w i - w j = 0 := by nlinarith [sq_nonneg (w i - w j)]
    omega

def Connected (B : ι → ι → ℤ) (i j : ι) : Prop :=
  Relation.ReflTransGen (fun a b => B a b ≠ 0) i j

theorem connected_refl (B : ι → ι → ℤ) (i : ι) : Connected B i i :=
  Relation.ReflTransGen.refl

theorem connected_trans {B : ι → ι → ℤ} {i j k : ι}
    (hij : Connected B i j) (hjk : Connected B j k) : Connected B i k :=
  hij.trans hjk

theorem connected_symm (B : ι → ι → ℤ) (hB : ∀ i j, B i j = B j i)
    {i j : ι} (h : Connected B i j) : Connected B j i := by
  induction h with
  | refl => exact .refl
  | tail h hjk ih =>
    exact (Relation.ReflTransGen.single (by simpa [hB] using hjk)).trans ih

theorem energy_zero_constant_on_component (B : ι → ι → ℤ)
    (hB : ∀ i j, B i j = B j i) (hn : ∀ i j, 0 ≤ B i j)
    (R : ℤ) (hc : ∀ i, rowSum B i ≤ R)
    (w : ι → ℤ) (hz : energy B R w = 0) {i j : ι} (hij : Connected B i j) :
    w i = w j := by
  have hr := (energy_eq_zero_rigidity B hB hn R hc w hz).2
  induction hij with
  | refl => rfl
  | tail h hjk ih => exact ih.trans (hr _ _ hjk)

end SparseComponent
