import SparseComponent.TotalFamily.Peeling

namespace SparseComponent.TotalFamily
open Finset Matrix Real TotalOnes
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

noncomputable def degreeLinear (r d : ℝ) : ℝ :=
  (r^2/(2*(r-1)) + gamma r*r^2*(r-1)) + gamma r*r^4/(2*d^2) - balance r*d
noncomputable def degreeConstant (r d : ℝ) : ℝ :=
  log (d/r) - slope r*(d-r) - gamma r*r^2
noncomputable def negativeGap (r d u : ℝ) : ℝ :=
  -gamma r*r^4*u^2 + degreeLinear r d*u + degreeConstant r d

theorem base_minus_balance (r : ℝ) (hr : r ≠ 0) : baseValue r-balance r = gamma r*r^2 := by
  by_cases h1 : r = 1
  · subst r
    norm_num [baseValue, vertex, balance, logB, gamma, logGamma]
  have ht : r-1 ≠ 0 := sub_ne_zero.mpr h1
  unfold baseValue vertex balance logB gamma
  rw [div_self hr, log_one]
  field_simp [ht]
  ring

theorem negativeGap_eq_neg_deficit (r d u : ℝ) (hr : r ≠ 0) :
    negativeGap r d u = -deficit r d u := by
  have hb := base_minus_balance r hr
  unfold negativeGap degreeLinear degreeConstant deficit vertex logB
  simp only [gamma, div_eq_mul_inv, _root_.mul_inv_rev] at *
  nlinarith [hb]

theorem deficit_plane_degree (r u : ℝ) (hr : r ≠ 0) :
    deficit r r u = gamma r*r^4*(u-1/r)^2 := by
  have h := deficit_tangent_identity r r u (1/r)
  rw [deficit_plane r hr, deficitDerivative_plane r hr] at h
  simpa using h

/-- Fully proved rational discriminant gate, uniform in the quadratic coefficient. -/
theorem negative_quadratic_gate (G L C gl lu cu u : ℝ)
    (hG : 0 < G) (hgl : gl ≤ G) (hL0 : 0 ≤ L) (hL : L ≤ lu)
    (hC : C ≤ cu) (hcu : cu ≤ 0) (gate : lu^2+4*gl*cu < 0) :
    -G*u^2+L*u+C < 0 := by
  have hsq : L^2 ≤ lu^2 := by nlinarith
  have hgc : G*C ≤ gl*cu := calc
    _ ≤ G*cu := mul_le_mul_of_nonneg_left hC hG.le
    _ ≤ gl*cu := mul_le_mul_of_nonpos_right hgl hcu
  have hp : 0 < 4*G := by positivity
  apply (mul_lt_mul_iff_right₀ hp).mp
  have he : 4*G*(-G*u^2+L*u+C) = -(2*G*u-L)^2+L^2+4*G*C := by ring
  rw [mul_zero, he]
  nlinarith [sq_nonneg (2*G*u-L)]

theorem degreeLinear_tail (r D d : ℝ) (hr : 2 ≤ r) (hD : 0 < D) (hd : D ≤ d)
    (hb : 0 ≤ balance r) : degreeLinear r d ≤ degreeLinear r D := by
  have hsq : D^2 ≤ d^2 := by nlinarith
  have hfrac : gamma r*r^4/(2*d^2) ≤ gamma r*r^4/(2*D^2) := by
    apply div_le_div_of_nonneg_left (by have := gamma_positive r hr; positivity) (by positivity)
    linarith
  have hbal := mul_le_mul_of_nonneg_left hd hb
  unfold degreeLinear
  linarith

theorem degreeConstant_tail (r D d : ℝ) (hr : 0 < r) (hD : 0 < D) (hd : D ≤ d)
    (hs : 1/D ≤ slope r) : degreeConstant r d ≤ degreeConstant r D := by
  have hp : 0 < d/D := div_pos (lt_of_lt_of_le hD hd) hD
  have hl := log_le_sub_one_of_pos hp
  have he : log (d/r) = log (d/D)+log (D/r) := by
    rw [← log_mul hp.ne' (div_ne_zero hD.ne' hr.ne')]
    congr 1
    field_simp
  have hterm := mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr hd)
  unfold degreeConstant
  rw [he]
  have hf : d/D-1 = (d-D)*(1/D) := by field_simp
  rw [hf] at hl
  nlinarith

theorem tail_gap_negative (r D d u : ℝ) (hr : 2 ≤ r) (hD : 0 < D) (hd : D ≤ d)
    (hu : 0 ≤ u) (hb : 0 ≤ balance r) (hs : 1/D ≤ slope r)
    (hL : degreeLinear r D ≤ 0) (hC : degreeConstant r D < 0) :
    negativeGap r d u < 0 := by
  have hld := (degreeLinear_tail r D d hr hD hd hb).trans hL
  have hcd := (degreeConstant_tail r D d (by linarith) hD hd hs).trans_lt hC
  have ht := mul_nonpos_of_nonpos_of_nonneg hld hu
  have hg : 0 ≤ gamma r*r^4*u^2 := by have := gamma_positive r hr; positivity
  unfold negativeGap
  nlinarith

/-- A vertex certificate is sufficient when the stronger separable method succeeds. -/
theorem vertex_minimum_degree_bound (r : ℝ) (hr : 2 ≤ r)
    (hcert : ∀ d : ℤ, 2 ≤ d → ∀ u : ℝ, 0 ≤ u → 0 ≤ deficit r d u)
    (A : Matrix ι ι ℤ) (hA : Binary A) (hdet : A.det ≠ 0)
    (hd : ∀ i, 2 ≤ rowDegree A i) (hc : ∀ j, 2 ≤ columnDegree A j) :
    |(A.det:ℝ)| ≤ exp ((Fintype.card ι:ℝ)*rate r + slope r*((edgeCount A:ℝ)-r*(Fintype.card ι:ℝ))) := by
  have hdp (i : ι) : 0 < rowDegree A i := by linarith [hd i]
  have hcp (j : ι) : 0 < columnDegree A j := by linarith [hc j]
  have hs := matrix_log_deficit r hr A hA hdet hdp hcp
  have hrow : 0 ≤ ∑ i, deficit r (rowSize A i) (rowMass A i) :=
    sum_nonneg fun i _ => hcert _ (hd i) _ (rowMass_nonneg A hA hdp hcp i)
  have hcol : 0 ≤ ∑ j, deficit r (columnSize A j) (columnMass A j) :=
    sum_nonneg fun j _ => hcert _ (hc j) _ (columnMass_nonneg A hA hdp hcp j)
  apply (log_le_iff_le_exp (abs_pos.mpr (by exact_mod_cast hdet))).mp
  linarith

theorem determinant_from_vertex_certificate (r : ℝ) (hr : 2 < r)
    (hcert : ∀ d : ℤ, 2 ≤ d → ∀ u : ℝ, 0 ≤ u → 0 ≤ deficit r d u)
    (hpeel : slope r*(r-1) < rate r)
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) (hA : Binary A) :
    |(A.det:ℝ)| ≤ exp (exponent r n (edgeCount A)) := by
  induction n with
  | zero => simp [exponent, edgeCount]
  | succ n ih =>
    by_cases hdet : A.det = 0
    · simpa only [hdet, Int.cast_zero, abs_zero] using (exp_pos (exponent r (n+1) (edgeCount A))).le
    by_cases hd : ∀ i, 2 ≤ rowDegree A i
    · by_cases hc : ∀ j, 2 ≤ columnDegree A j
      · simpa only [Fintype.card_fin, exponent] using
          vertex_minimum_degree_bound r hr.le hcert A hA hdet hd hc
      · obtain ⟨j, hj⟩ := not_forall.mp hc
        have hp := columnDegree_pos_of_det_ne_zero A hA hdet j
        have hk : columnDegree A j = 1 := by omega
        exact (column_peel_strict r (slope_pos r hr).le A hA j hp
          (by simpa [hk] using hpeel) ih).le
    · obtain ⟨i, hi⟩ := not_forall.mp hd
      have hp := rowDegree_pos_of_det_ne_zero A hA hdet i
      have hk : rowDegree A i = 1 := by omega
      exact (row_peel_strict r (slope_pos r hr).le A hA i hp
        (by simpa [hk] using hpeel) ih).le
end SparseComponent.TotalFamily
