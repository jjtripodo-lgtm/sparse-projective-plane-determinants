import SparseComponent.TotalFamily.Spectral

namespace SparseComponent.TotalFamily
open Finset Matrix Real TotalOnes
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

noncomputable def slope (r : ℝ) : ℝ := 1/r - 1/(2*(r-1)) + (r-1/2)*gamma r
noncomputable def balance (r : ℝ) : ℝ := r/(2*(r-1)) - gamma r*(r^2+r/2)
noncomputable def vertex (r d u : ℝ) : ℝ :=
  (logB (r-1) (r^2)*r^2/2 + gamma r*r^4/(2*d^2))*u - gamma r*r^4*u^2 + log (d/r)
noncomputable def baseValue (r : ℝ) : ℝ := vertex r r (1/r)
noncomputable def rate (r : ℝ) : ℝ :=
  (log r + ((planeOrder r-1)/2)*log (r-1))/planeOrder r
noncomputable def deficit (r d u : ℝ) : ℝ :=
  baseValue r + slope r*(d-r) + balance r*(d*u-1) - vertex r d u
noncomputable def deficitDerivative (r d u : ℝ) : ℝ :=
  balance r*d - (logB (r-1) (r^2)*r^2/2 + gamma r*r^4/(2*d^2)) + 2*gamma r*r^4*u

/-- The explicit edge slope is positive throughout the density range. -/
theorem slope_pos (r : ℝ) (hr : 2 < r) : 0 < slope r := by
  have hp : 0 < r := by linarith
  have ht : 0 < r-1 := by linarith
  have hfirst : 0 < 1/r - 1/(2*(r-1)) := by
    apply sub_pos.mpr
    apply (div_lt_div_iff₀ (by positivity : 0 < 2*(r-1)) hp).mpr
    nlinarith
  have hg := gamma_positive r hr.le
  unfold slope
  exact add_pos hfirst (mul_pos (by linarith) hg)

theorem base_identity (r : ℝ) (hr : 2 ≤ r) :
    logA (r-1) (r^2) + 2*baseValue r = 2*rate r := by
  have hrp : 0 < r := by linarith
  have hb : 2*baseValue r = logB (r-1) (r^2)*r-gamma r*(2*r^2-r) := by
    unfold baseValue vertex
    rw [div_self hrp.ne', log_one]
    field_simp
    ring
  have h := base_polynomial_value r hr
  change logA (r-1) (r^2)+logB (r-1) (r^2)*r-gamma r*(2*r^2-r) = 2*rate r at h
  linarith

theorem deficit_plane (r : ℝ) (hr : r ≠ 0) : deficit r r (1/r) = 0 := by
  simp [deficit, baseValue, hr]

theorem deficitDerivative_plane (r : ℝ) (hr : r ≠ 0) :
    deficitDerivative r r (1/r) = 0 := by
  by_cases h1 : r = 1
  · subst r
    norm_num [deficitDerivative, balance, logB, gamma, logGamma]
  have ht : r-1 ≠ 0 := sub_ne_zero.mpr h1
  unfold deficitDerivative balance logB gamma
  field_simp [ht]
  ring

/-- Exact remainder of the supporting tangent. This is uniform in every real degree/mass. -/
theorem deficit_tangent_identity (r d u a : ℝ) :
    deficit r d u - (deficit r d a + deficitDerivative r d a*(u-a)) =
      gamma r*r^4*(u-a)^2 := by
  unfold deficit deficitDerivative vertex
  ring

theorem deficit_tangent_le (r : ℝ) (hr : 2 ≤ r) (d u a : ℝ) :
    deficit r d a + deficitDerivative r d a*(u-a) ≤ deficit r d u := by
  have h := deficit_tangent_identity r d u a
  have hn : 0 ≤ gamma r*r^4*(u-a)^2 := by
    have := gamma_positive r hr
    positivity
  linarith

theorem sum_vertex_expansion (r : ℝ) (d u : ι → ℝ) :
    (∑ i, vertex r (d i) (u i)) =
      (r^2*logB (r-1) (r^2)/2)*(∑ i, u i) +
      (r^4*gamma r/2)*(∑ i, u i/(d i)^2) -
      r^4*gamma r*(∑ i, (u i)^2) + (∑ i, log (d i/r)) := by
  have he (i : ι) : vertex r (d i) (u i) =
      (r^2*logB (r-1) (r^2)/2)*u i+(r^4*gamma r/2)*(u i/(d i)^2)-
      r^4*gamma r*(u i)^2+log (d i/r) := by
    unfold vertex
    simp only [div_eq_mul_inv, _root_.mul_inv_rev]
    ring
  simp_rw [he]
  simp only [sum_add_distrib, sum_sub_distrib, mul_sum]

/-- Matrix-to-vertex bridge without individual degree caps or supplied spectral hypotheses. -/
theorem matrix_separable (r : ℝ) (hr : 2 ≤ r) (A : Matrix ι ι ℤ) (hA : Binary A)
    (hdet : A.det ≠ 0) (hd : ∀ i, 0 < rowDegree A i) (hc : ∀ j, 0 < columnDegree A j) :
    2*log |(A.det:ℝ)| ≤ (Fintype.card ι:ℝ)*logA (r-1) (r^2) +
      (∑ i, vertex r (rowSize A i) (rowMass A i)) +
      (∑ j, vertex r (columnSize A j) (columnMass A j)) := by
  have hn := normalized_log_det r (by linarith) A hdet hd hc
  have hs := logdet_hermite r hr A hA hdet hd hc
  rw [gram_trace r A hA hd hc] at hs
  have hm := mul_le_mul_of_nonneg_left
    (gram_second_moment_lower r A hA hd hc) (gamma_positive r hr).le
  have hz := sum_rowMass_eq_columnMass A
  rw [sum_vertex_expansion, sum_vertex_expansion, ← hz]
  nlinarith

theorem sum_deficit_expansion (r : ℝ) (d u : ι → ℝ)
    (hu : ∑ i, d i*u i = (Fintype.card ι:ℝ)) :
    (∑ i, deficit r (d i) (u i)) = (Fintype.card ι:ℝ)*baseValue r +
      slope r*((∑ i, d i)-r*(Fintype.card ι:ℝ)) - (∑ i, vertex r (d i) (u i)) := by
  simp only [deficit, sum_sub_distrib, sum_add_distrib, sum_const, card_univ, nsmul_eq_mul,
    ← mul_sum, hu]
  ring

/-- Full vertex-deficit inequality, uniformly for every density r >= 2. -/
theorem matrix_log_deficit (r : ℝ) (hr : 2 ≤ r) (A : Matrix ι ι ℤ) (hA : Binary A)
    (hdet : A.det ≠ 0) (hd : ∀ i, 0 < rowDegree A i) (hc : ∀ j, 0 < columnDegree A j) :
    log |(A.det:ℝ)| ≤ (Fintype.card ι:ℝ)*rate r + slope r*((edgeCount A:ℝ)-r*(Fintype.card ι:ℝ)) -
      ((∑ i, deficit r (rowSize A i) (rowMass A i)) +
       (∑ j, deficit r (columnSize A j) (columnMass A j)))/2 := by
  have hs := matrix_separable r hr A hA hdet hd hc
  rw [sum_deficit_expansion r _ _ (weighted_row_balance A hd hc),
    sum_deficit_expansion r _ _ (weighted_column_balance A hd hc)]
  have hrow : (∑ i, rowSize A i) = (edgeCount A:ℝ) := by simp [rowSize, edgeCount]
  have hcol : (∑ j, columnSize A j) = (edgeCount A:ℝ) := by
    simp only [columnSize, columnDegree, edgeCount, rowDegree, Int.cast_sum]
    exact sum_comm
  rw [hrow, hcol]
  have hb := congrArg (fun z : ℝ => (Fintype.card ι:ℝ)*z) (base_identity r hr)
  nlinarith
end SparseComponent.TotalFamily
