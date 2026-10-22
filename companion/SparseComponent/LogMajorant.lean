import SparseComponent.Hermite
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

namespace SparseComponent
open Real

noncomputable def quadratic (a b c x : ℝ) : ℝ := a + b * x + c * x ^ 2

noncomputable def hermiteError (a b c t R k x : ℝ) : ℝ :=
  quadratic a b c x - log x - k * ((x - t) ^ 2 * (R - x))

noncomputable def hermiteError1 (b c t R k x : ℝ) : ℝ :=
  b + 2 * c * x - x⁻¹ - k * (2 * (x - t) * (R - x) - (x - t) ^ 2)

noncomputable def hermiteError2 (c t R k x : ℝ) : ℝ :=
  2 * c + (x ^ 2)⁻¹ - k * (2 * R + 4 * t - 6 * x)

noncomputable def hermiteError3 (k x : ℝ) : ℝ := -2 / x ^ 3 + 6 * k

theorem hermiteError_deriv (a b c t R k x : ℝ) (hx : 0 < x) :
    HasDerivAt (hermiteError a b c t R k) (hermiteError1 b c t R k x) x := by
  have hp : HasDerivAt (fun y : ℝ => (y - t) ^ 2 * (R - y))
      (2 * (x - t) * (R - x) - (x - t) ^ 2) x := by
    convert! (((hasDerivAt_id x).sub_const t).pow 2).mul ((hasDerivAt_const x R).sub (hasDerivAt_id x)) using 1 <;> (try dsimp) <;> ring
  have hq : HasDerivAt (quadratic a b c) (b + 2 * c * x) x := by
    convert! (((hasDerivAt_const x a).add ((hasDerivAt_id x).const_mul b)).add
      (((hasDerivAt_id x).pow 2).const_mul c)) using 1 <;> dsimp [quadratic] <;> ring
  convert! (hq.sub (Real.hasDerivAt_log hx.ne')).sub (hp.const_mul k) using 1

theorem hermiteError1_deriv (b c t R k x : ℝ) (hx : 0 < x) :
    HasDerivAt (hermiteError1 b c t R k) (hermiteError2 c t R k x) x := by
  have hp : HasDerivAt (fun y : ℝ => 2 * (y - t) * (R - y) - (y - t) ^ 2)
      (2 * R + 4 * t - 6 * x) x := by
    convert! ((((hasDerivAt_id x).sub_const t).const_mul 2).mul
      ((hasDerivAt_const x R).sub (hasDerivAt_id x))).sub
        (((hasDerivAt_id x).sub_const t).pow 2) using 1 <;> (try dsimp) <;> ring
  convert! ((((hasDerivAt_id x).const_mul (2 * c)).const_add b).sub
    (hasDerivAt_inv hx.ne')).sub (hp.const_mul k) using 1
  dsimp [hermiteError2]
  ring

theorem hermiteError2_deriv (c t R k x : ℝ) (hx : 0 < x) :
    HasDerivAt (hermiteError2 c t R k) (hermiteError3 k x) x := by
  have hp : HasDerivAt (fun y : ℝ => 2 * R + 4 * t - 6 * y) (-6) x := by
    convert! (hasDerivAt_const x (2 * R + 4 * t)).sub ((hasDerivAt_id x).const_mul 6) using 1 <;> (try dsimp) <;> ring
  convert! (((((hasDerivAt_id x).pow 2).inv (pow_ne_zero 2 hx.ne')).const_add (2 * c)).sub
    (hp.const_mul k)) using 1
  dsimp [hermiteError3]
  field_simp
  ring

/-- Quantitative Hermite upper bound for log, proved by three Rolle steps. -/
theorem quadratic_log_majorant (a b c t R : ℝ) (ht : 0 < t) (htR : t < R)
    (hqt : quadratic a b c t = log t) (hqR : quadratic a b c R = log R)
    (hdt : b + 2 * c * t = t⁻¹)
    (x : ℝ) (hx : 0 < x) (hxR : x ≤ R) :
    (x - t) ^ 2 * (R - x) / (3 * R ^ 3) ≤ quadratic a b c x - log x := by
  by_cases hxt : x = t
  · subst x
    simp [hqt]
  by_cases hxEq : x = R
  · subst x
    simp [hqR]
  have hxR' : x < R := lt_of_le_of_ne hxR hxEq
  have hR : 0 < R := ht.trans htR
  have hp : 0 < (x - t) ^ 2 * (R - x) :=
    mul_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hxt)) (sub_pos.mpr hxR')
  let k := (quadratic a b c x - log x) / ((x - t) ^ 2 * (R - x))
  have hft : hermiteError a b c t R k t = 0 := by simp [hermiteError, hqt]
  have hfR : hermiteError a b c t R k R = 0 := by simp [hermiteError, hqR]
  have hfx : hermiteError a b c t R k x = 0 := by
    unfold hermiteError k
    rw [div_mul_cancel₀ _ hp.ne']
    ring
  have hfdt : hermiteError1 b c t R k t = 0 := by simp [hermiteError1, hdt]
  obtain ⟨ξ, hξ, hξR, hzero⟩ := hermite_third_derivative_zero
    (hermiteError_deriv a b c t R k) (hermiteError1_deriv b c t R k)
    (hermiteError2_deriv c t R k) ht htR hx hxR' hxt hft hfR hfx hfdt
  have hk : 1 / (3 * ξ ^ 3) = k := by
    unfold hermiteError3 at hzero
    have hξ3 : ξ ^ 3 ≠ 0 := pow_ne_zero _ hξ.ne'
    field_simp at hzero ⊢
    nlinarith
  have hc : 1 / (3 * R ^ 3) ≤ k := by
    rw [← hk]
    apply one_div_le_one_div_of_le (by positivity)
    have := pow_le_pow_left₀ hξ.le hξR.le 3
    linarith
  have hmul := mul_le_mul_of_nonneg_right hc hp.le
  dsimp [k] at hmul
  rw [div_mul_cancel₀ _ hp.ne'] at hmul
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul

end SparseComponent
