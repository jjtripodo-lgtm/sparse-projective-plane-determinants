import SparseComponent.Partition

namespace SparseComponent
open Finset
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [LinearOrder ι]

def chooseTwo (b : ℤ) : ℤ := b * (b - 1) / 2

theorem chooseTwo_nonneg (b : ℤ) (hb : 0 ≤ b) : 0 ≤ chooseTwo b := by
  unfold chooseTwo
  apply Int.ediv_nonneg _ (by norm_num)
  by_cases h : b = 0
  · simp [h]
  · have : 0 ≤ b - 1 := by omega
    exact mul_nonneg hb this

theorem chooseTwo_pos (b : ℤ) (hb : 2 ≤ b) : 1 ≤ chooseTwo b := by
  apply (Int.le_ediv_iff_mul_le (by norm_num : (0 : ℤ) < 2)).mpr
  nlinarith

theorem chooseTwo_zero_iff (b : ℤ) (hb : 0 ≤ b) : chooseTwo b = 0 ↔ b ≤ 1 := by
  constructor
  · intro h
    by_contra h'
    have := chooseTwo_pos b (by omega)
    omega
  · intro h
    have : b = 0 ∨ b = 1 := by omega
    rcases this with h | h <;> simp [chooseTwo, h]

def cycleWeight (A : ι → κ → ℤ) (i j : ι) : ℤ :=
  if i < j then chooseTwo (gram A i j) else 0

def cycleCountOn (A : ι → κ → ℤ) (C : Finset ι) : ℤ :=
  ∑ i ∈ C, ∑ j ∈ C, cycleWeight A i j

def cycleCount (A : ι → κ → ℤ) : ℤ := ∑ i, ∑ j, cycleWeight A i j

theorem cycleWeight_nonneg (A : ι → κ → ℤ) (hA : Binary A) (i j : ι) :
    0 ≤ cycleWeight A i j := by
  unfold cycleWeight
  split_ifs
  · exact chooseTwo_nonneg _ (gram_nonneg A hA i j)
  · rfl

theorem cycleCountOn_nonneg (A : ι → κ → ℤ) (hA : Binary A) (C : Finset ι) :
    0 ≤ cycleCountOn A C :=
  sum_nonneg fun i _ => sum_nonneg fun j _ => cycleWeight_nonneg A hA i j

theorem cycleCountOn_zero_overlap (A : ι → κ → ℤ) (hA : Binary A)
    (C : Finset ι) (hz : cycleCountOn A C = 0) {i j : ι}
    (hi : i ∈ C) (hj : j ∈ C) (hne : i ≠ j) : gram A i j ≤ 1 := by
  have hz' : ∀ i ∈ C, ∀ j ∈ C, cycleWeight A i j = 0 := by
    intro i hi
    have hs := (sum_eq_zero_iff_of_nonneg
      (fun i _ => sum_nonneg fun j _ => cycleWeight_nonneg A hA i j)).mp hz i hi
    exact (sum_eq_zero_iff_of_nonneg (fun j _ => cycleWeight_nonneg A hA i j)).mp hs
  rcases lt_or_gt_of_ne hne with h | h
  · have hw := hz' i hi j hj
    rw [cycleWeight, if_pos h] at hw
    exact (chooseTwo_zero_iff _ (gram_nonneg A hA i j)).mp hw
  · have hw := hz' j hj i hi
    rw [cycleWeight, if_pos h] at hw
    rw [gram_symm]
    exact (chooseTwo_zero_iff _ (gram_nonneg A hA j i)).mp hw

theorem cycleWeight_eq_zero_of_gram_zero (A : ι → κ → ℤ) (i j : ι)
    (h : gram A i j = 0) : cycleWeight A i j = 0 := by
  simp [cycleWeight, h, chooseTwo]

theorem sum_component_cycles (A : ι → κ → ℤ) (i : ι) {j : ι}
    (hj : j ∈ component A i) :
    (∑ k ∈ component A i, cycleWeight A j k) = ∑ k, cycleWeight A j k := by
  apply sum_subset (subset_univ _)
  intro k hk hkC
  exact cycleWeight_eq_zero_of_gram_zero A j k (component_gram_closed A i hj hkC)

theorem cycleCount_partition (A : ι → κ → ℤ) :
    (∑ C ∈ components A, cycleCountOn A C) = cycleCount A := by
  unfold cycleCountOn cycleCount
  calc
    _ = ∑ C ∈ components A, ∑ j ∈ C, ∑ k, cycleWeight A j k := by
      apply sum_congr rfl
      intro C hC
      obtain ⟨i, rfl⟩ := (mem_components A C).mp hC
      apply sum_congr rfl
      exact fun j hj => sum_component_cycles A i hj
    _ = _ := sum_components A _

end SparseComponent
