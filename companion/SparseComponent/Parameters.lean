import SparseComponent.LogBounds

namespace SparseComponent
open Real

noncomputable def logGamma (t R : ℝ) : ℝ :=
  ((R - t) / t - (log R - log t)) / (R - t) ^ 2

noncomputable def logA (t R : ℝ) : ℝ := log t - 1 - logGamma t R * t ^ 2
noncomputable def logB (t R : ℝ) : ℝ := t⁻¹ + 2 * logGamma t R * t

theorem log_interpolation_t (t R : ℝ) (ht : 0 < t) :
    quadratic (logA t R) (logB t R) (-logGamma t R) t = log t := by
  unfold quadratic logA logB
  field_simp
  ring

theorem log_interpolation_R (t R : ℝ) (ht : 0 < t) (htR : t < R) :
    quadratic (logA t R) (logB t R) (-logGamma t R) R = log R := by
  have hne : R - t ≠ 0 := ne_of_gt (sub_pos.mpr htR)
  unfold quadratic logA logB logGamma
  field_simp
  ring

theorem log_interpolation_deriv (t R : ℝ) :
    logB t R + 2 * (-logGamma t R) * t = t⁻¹ := by
  unfold logB
  ring

theorem explicit_log_majorant (t R : ℝ) (ht : 0 < t) (htR : t < R)
    (x : ℝ) (hx : 0 < x) (hxR : x ≤ R) :
    log x + (x - t) ^ 2 * (R - x) / (3 * R ^ 3) ≤
      logA t R + logB t R * x - logGamma t R * x ^ 2 := by
  have h := quadratic_log_majorant (logA t R) (logB t R) (-logGamma t R) t R ht htR
    (log_interpolation_t t R ht) (log_interpolation_R t R ht htR)
    (log_interpolation_deriv t R) x hx hxR
  unfold quadratic at h
  linarith

/-- Uniform positive lower bound on the Hermite curvature coefficient. -/
theorem logGamma_lower (t R : ℝ) (ht : 0 < t) (htR : t < R) :
    1 / (2 * t * R) ≤ logGamma t R := by
  have hR : 0 < R := ht.trans htR
  have hdiff : 0 < R - t := sub_pos.mpr htR
  have hratio : 1 ≤ R / t := (le_div_iff₀ ht).mpr (by linarith)
  have hlog := log_le_half_sub_inv (R / t) hratio
  rw [log_div hR.ne' ht.ne'] at hlog
  calc
    1 / (2 * t * R) = (((R - t) / t - (R / t - (R / t)⁻¹) / 2) / (R - t) ^ 2) := by
      field_simp
      ring
    _ ≤ logGamma t R := by
      unfold logGamma
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      linarith

noncomputable def planeOrder (r : ℝ) : ℝ := r ^ 2 - r + 1
noncomputable def gamma (r : ℝ) : ℝ := logGamma (r - 1) (r ^ 2)
noncomputable def delta (r : ℝ) : ℝ := (r - 1)⁻¹ - (2 * r + 1) * gamma r
noncomputable def stabilityCoefficient (r : ℝ) : ℝ := 1 / (6 * r ^ 6)

theorem planeOrder_positive (r : ℝ) : 0 < planeOrder r := by
  unfold planeOrder
  nlinarith [sq_nonneg (r - 1 / 2)]

theorem gamma_lower (r : ℝ) (hr : 2 ≤ r) :
    1 / (2 * (r - 1) * r ^ 2) ≤ gamma r := by
  apply logGamma_lower
  · linarith
  · nlinarith [sq_nonneg r]

theorem gamma_positive (r : ℝ) (hr : 2 ≤ r) : 0 < gamma r := by
  have h := gamma_lower r hr
  have ht : 0 < r - 1 := by linarith
  have hr0 : 0 < r := by linarith
  have : 0 < 1 / (2 * (r - 1) * r ^ 2) := by positivity
  exact this.trans_le h

/-- Exact algebraic decomposition used to handle the two small degree caps separately. -/
theorem delta_decomposition (r : ℝ) (hr : 2 ≤ r) :
    delta r = r * (r - 3) / ((r - 1) * planeOrder r) +
      (2 * r + 1) * log (r ^ 2 / (r - 1)) / planeOrder r ^ 2 := by
  have hr0 : 0 < r := by linarith
  have ht : 0 < r - 1 := by linarith
  have hv := planeOrder_positive r
  rw [log_div (pow_ne_zero _ hr0.ne') ht.ne']
  unfold delta gamma logGamma planeOrder at *
  have hD : r ^ 2 - (r - 1) ≠ 0 := by nlinarith
  field_simp [hD]
  ring

noncomputable def blockLogRate (r : ℝ) : ℝ :=
  (log r + (planeOrder r - 1) / 2 * log (r - 1)) / planeOrder r

theorem tangent_coefficient (r : ℝ) :
    logB (r - 1) (r ^ 2) - (4 * r - 1) * gamma r = delta r := by
  simp only [logB, delta, gamma]
  ring

theorem base_polynomial_value (r : ℝ) (hr : 2 ≤ r) :
    logA (r - 1) (r ^ 2) + logB (r - 1) (r ^ 2) * r - gamma r * (2 * r ^ 2 - r) =
      2 * blockLogRate r := by
  have hr0 : 0 < r := by linarith
  have ht : 0 < r - 1 := by linarith
  have hv := planeOrder_positive r
  have hD : r ^ 2 - (r - 1) ≠ 0 := by nlinarith
  unfold logA logB gamma logGamma blockLogRate planeOrder at *
  rw [log_pow]
  field_simp [hD]
  ring

end SparseComponent
