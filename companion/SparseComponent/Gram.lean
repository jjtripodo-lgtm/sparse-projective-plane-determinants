import SparseComponent.Energy

namespace SparseComponent
open Finset
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def Binary (A : ι → κ → ℤ) : Prop := ∀ i k, A i k = 0 ∨ A i k = 1

def rowDegree (A : ι → κ → ℤ) (i : ι) : ℤ := ∑ k, A i k

def columnDegree (A : ι → κ → ℤ) (k : κ) : ℤ := ∑ i, A i k

def gram (A : ι → κ → ℤ) (i j : ι) : ℤ := ∑ k, A i k * A j k

theorem binary_nonneg (A : ι → κ → ℤ) (hA : Binary A) (i : ι) (k : κ) :
    0 ≤ A i k := by rcases hA i k with h | h <;> omega

theorem binary_le_one (A : ι → κ → ℤ) (hA : Binary A) (i : ι) (k : κ) :
    A i k ≤ 1 := by rcases hA i k with h | h <;> omega

theorem gram_symm (A : ι → κ → ℤ) (i j : ι) : gram A i j = gram A j i := by
  unfold gram
  apply sum_congr rfl
  intros
  ring

theorem gram_nonneg (A : ι → κ → ℤ) (hA : Binary A) (i j : ι) :
    0 ≤ gram A i j :=
  sum_nonneg fun k _ => mul_nonneg (binary_nonneg A hA i k) (binary_nonneg A hA j k)

theorem gram_diagonal (A : ι → κ → ℤ) (hA : Binary A) (i : ι) :
    gram A i i = rowDegree A i := by
  unfold gram rowDegree
  apply sum_congr rfl
  intro k hk
  rcases hA i k with h | h <;> simp [h]

theorem gram_rowSum (A : ι → κ → ℤ) (i : ι) :
    rowSum (gram A) i = ∑ k, A i k * columnDegree A k := by
  unfold rowSum gram columnDegree
  rw [sum_comm]
  simp only [mul_sum]

theorem gram_rowSum_le (A : ι → κ → ℤ) (hA : Binary A)
    (r : ℤ) (hc : ∀ k, columnDegree A k ≤ r) (i : ι) :
    rowSum (gram A) i ≤ r * rowDegree A i := by
  rw [gram_rowSum, rowDegree, mul_sum]
  apply sum_le_sum
  intro k hk
  nlinarith [binary_nonneg A hA i k, hc k]

theorem gram_rowSum_cap (A : ι → κ → ℤ) (hA : Binary A)
    (r : ℤ) (hr : 0 ≤ r) (hc : ∀ k, columnDegree A k ≤ r)
    (hd : ∀ i, rowDegree A i ≤ r) (i : ι) : rowSum (gram A) i ≤ r ^ 2 := by
  have := gram_rowSum_le A hA r hc i
  have := mul_le_mul_of_nonneg_left (hd i) hr
  nlinarith

theorem rowDegree_of_saturated_gram (A : ι → κ → ℤ) (hA : Binary A)
    (r : ℤ) (hr : 0 < r) (hc : ∀ k, columnDegree A k ≤ r)
    (hd : ∀ i, rowDegree A i ≤ r) (i : ι)
    (hs : rowSum (gram A) i = r ^ 2) : rowDegree A i = r := by
  have := gram_rowSum_le A hA r hc i
  have := hd i
  nlinarith

theorem incident_columnDegree_of_saturated_gram (A : ι → κ → ℤ) (hA : Binary A)
    (r : ℤ) (hr : 0 < r) (hc : ∀ k, columnDegree A k ≤ r)
    (hd : ∀ i, rowDegree A i ≤ r) (i : ι)
    (hs : rowSum (gram A) i = r ^ 2) (k : κ) (hik : A i k = 1) :
    columnDegree A k = r := by
  have hdeg := rowDegree_of_saturated_gram A hA r hr hc hd i hs
  have hz : (∑ k, A i k * (r - columnDegree A k)) = 0 := by
    simp only [mul_sub, sum_sub_distrib, ← sum_mul]
    rw [← gram_rowSum, hs, show (∑ k, A i k) = r from hdeg]
    ring
  have hk := (sum_eq_zero_iff_of_nonneg (fun k _ =>
    mul_nonneg (binary_nonneg A hA i k) (sub_nonneg.mpr (hc k)))).mp hz k (mem_univ k)
  rw [hik, one_mul] at hk
  omega

theorem gram_pos_of_shared_column (A : ι → κ → ℤ) (hA : Binary A)
    (i j : ι) (k : κ) (hi : A i k = 1) (hj : A j k = 1) :
    0 < gram A i j := by
  have h := single_le_sum (f := fun k => A i k * A j k)
    (fun k _ => mul_nonneg (binary_nonneg A hA i k) (binary_nonneg A hA j k)) (mem_univ k)
  simp only [hi, hj, one_mul] at h
  exact lt_of_lt_of_le (by norm_num) h

theorem connected_of_shared_column (A : ι → κ → ℤ) (hA : Binary A)
    (i j : ι) (k : κ) (hi : A i k = 1) (hj : A j k = 1) :
    Connected (gram A) i j :=
  Relation.ReflTransGen.single (ne_of_gt (gram_pos_of_shared_column A hA i j k hi hj))

noncomputable def component (A : ι → κ → ℤ) (i : ι) : Finset ι :=
  @Finset.filter ι (Connected (gram A) i) (Classical.decPred _) univ

@[simp] theorem mem_component (A : ι → κ → ℤ) (i j : ι) :
    j ∈ component A i ↔ Connected (gram A) i j := by simp [component]

theorem self_mem_component (A : ι → κ → ℤ) (i : ι) : i ∈ component A i :=
  (mem_component A i i).mpr (connected_refl _ _)

theorem gram_eq_zero_of_not_connected (A : ι → κ → ℤ) {i j : ι}
    (h : ¬ Connected (gram A) i j) : gram A i j = 0 := by
  by_contra h'
  exact h (Relation.ReflTransGen.single h')

end SparseComponent
