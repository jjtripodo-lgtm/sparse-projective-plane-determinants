import SparseComponent.Plane

namespace SparseComponent
open Finset
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [LinearOrder ι]

noncomputable def residualOn (A : ι → κ → ℤ) (r : ℤ) (C : Finset ι) : ℤ := by
  classical
  exact if PlaneRows A r C then 0 else C.card

def degreeDeficitOn (A : ι → κ → ℤ) (r : ℤ) (C : Finset ι) : ℤ :=
  ∑ i ∈ C, (r - rowDegree A i)

noncomputable def totalDefect (A : ι → κ → ℤ) (r : ℤ) : ℤ := ∑ i, localDefect A r i

def degreeDeficit (A : ι → κ → ℤ) (r : ℤ) : ℤ := ∑ i, (r - rowDegree A i)

noncomputable def badRows (A : ι → κ → ℤ) (r : ℤ) : Finset ι := by
  classical
  exact univ.filter (fun i => ¬ PlaneRows A r (component A i))

noncomputable def residualRows (A : ι → κ → ℤ) (r : ℤ) : ℤ := (badRows A r).card

theorem degreeDeficitOn_nonneg (A : ι → κ → ℤ) (r : ℤ)
    (hd : ∀ i, rowDegree A i ≤ r) (C : Finset ι) : 0 ≤ degreeDeficitOn A r C :=
  sum_nonneg fun i _ => sub_nonneg.mpr (hd i)

/-- Charge a nonplane component to positive integer diagonal defects, a C4, or the isolated exception. -/
theorem component_charge (A : ι → κ → ℤ) (hA : Binary A) (hinj : DistinctColumns A)
    (r : ℤ) (hr : 2 ≤ r) (hc : ∀ k, columnDegree A k ≤ r)
    (hd : ∀ i, rowDegree A i ≤ r) (i : ι) :
    residualOn A r (component A i) ≤
      (∑ j ∈ component A i, localDefect A r j) +
        (r ^ 2 - r + 1) * cycleCountOn A (component A i) +
        degreeDeficitOn A r (component A i) := by
  classical
  have hr' : 0 < r := by omega
  have hv : 0 ≤ r ^ 2 - r + 1 := by nlinarith
  have ht : 0 ≤ ∑ j ∈ component A i, localDefect A r j :=
    sum_nonneg fun j _ => localDefect_nonneg A hA r hr'.le hc hd j
  have hcy := cycleCountOn_nonneg A hA (component A i)
  have he := degreeDeficitOn_nonneg A r hd (component A i)
  have hvcy := mul_nonneg hv hcy
  by_cases hp : PlaneRows A r (component A i)
  · simp only [residualOn, if_pos hp]
    omega
  simp only [residualOn, if_neg hp]
  by_cases hpos : ∀ j ∈ component A i, 1 ≤ localDefect A r j
  · have hbound : ((component A i).card : ℤ) ≤ ∑ j ∈ component A i, localDefect A r j := by
      calc
        _ = ∑ j ∈ component A i, (1 : ℤ) := by simp
        _ ≤ _ := sum_le_sum hpos
    omega
  push Not at hpos
  obtain ⟨j, hj, hnj⟩ := hpos
  have hjz : localDefect A r j = 0 := by
    have := localDefect_nonneg A hA r hr'.le hc hd j
    omega
  have hcomp := component_eq_of_mem A hj
  by_cases hw : ∃ k, shiftedColumn A r j k ≠ 0
  · have hcard := zero_defect_component_card A hA r hr' hc hd j hjz hw
    have hcypos := zero_defect_nonplane_cycle_positive A hA r hr' hc hd j hjz hw
      (by rwa [hcomp])
    rw [hcomp] at hcard hcypos
    have hmul := mul_le_mul_of_nonneg_left hcypos hv
    nlinarith
  · push Not at hw
    have hex := zero_shifted_exception A hA hinj r hr j hw
    have hsingleton := zero_shifted_component_singleton A hA r j hw
    have hC : component A i = {j} := hcomp.symm.trans hsingleton
    have hE : degreeDeficitOn A r (component A i) = 1 := by
      simp [degreeDeficitOn, hC, hex.1, hex.2.1]
    rw [hC]
    simp only [card_singleton, Int.cast_ofNat]
    rw [hC] at ht hvcy hE
    omega

theorem residualRows_partition (A : ι → κ → ℤ) (r : ℤ) :
    (∑ C ∈ components A, residualOn A r C) = residualRows A r := by
  classical
  calc
    _ = ∑ C ∈ components A, ∑ i ∈ C, if PlaneRows A r (component A i) then (0 : ℤ) else 1 := by
      apply sum_congr rfl
      intro C hC
      obtain ⟨j, rfl⟩ := (mem_components A C).mp hC
      have hs : (∑ i ∈ component A j, if PlaneRows A r (component A i) then (0 : ℤ) else 1) =
          ∑ _i ∈ component A j, if PlaneRows A r (component A j) then (0 : ℤ) else 1 := by
        apply sum_congr rfl
        intro i hi
        rw [component_eq_of_mem A hi]
      rw [hs]
      unfold residualOn
      split_ifs <;> simp
    _ = ∑ i, if PlaneRows A r (component A i) then (0 : ℤ) else 1 := sum_components A _
    _ = residualRows A r := by
      unfold residualRows badRows
      simp [sum_ite, filter_not]

/-- The complete integer component-extraction bridge, with no spectral premises. -/
theorem integer_component_extraction (A : ι → κ → ℤ) (hA : Binary A)
    (hinj : DistinctColumns A) (r : ℤ) (hr : 2 ≤ r)
    (hc : ∀ k, columnDegree A k ≤ r) (hd : ∀ i, rowDegree A i ≤ r) :
    residualRows A r ≤ totalDefect A r +
      (r ^ 2 - r + 1) * cycleCount A + degreeDeficit A r := by
  rw [← residualRows_partition]
  have hsum : (∑ C ∈ components A, residualOn A r C) ≤
      ∑ C ∈ components A, ((∑ j ∈ C, localDefect A r j) +
        (r ^ 2 - r + 1) * cycleCountOn A C + degreeDeficitOn A r C) :=
    sum_le_sum (s := components A) (fun C hC => by
    obtain ⟨i, rfl⟩ := (mem_components A C).mp hC
    exact component_charge A hA hinj r hr hc hd i)
  simp only [sum_add_distrib, ← mul_sum] at hsum
  rw [sum_components, cycleCount_partition] at hsum
  have hE : (∑ C ∈ components A, degreeDeficitOn A r C) = degreeDeficit A r :=
    sum_components A _
  rw [hE] at hsum
  exact hsum

end SparseComponent
