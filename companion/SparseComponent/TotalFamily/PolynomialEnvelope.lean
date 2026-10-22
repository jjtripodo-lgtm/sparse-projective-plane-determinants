import SparseComponent.TotalFamily.FiniteCertificateTools

namespace SparseComponent.TotalFamily
open Finset Real

def intervalCoefficient (a b gl gh : ℚ) : ℚ := min (a+b*gl) (a+b*gh)
def boxTerm (a b gl gh U : ℚ) (i j : ℕ) : ℚ :=
  if i+j=0 then intervalCoefficient a b gl gh
  else min 0 (intervalCoefficient a b gl gh*U^i*U^j)
def boxEnvelope {ι : Type*} [Fintype ι] (a b : ι → ℚ) (ix iy : ι → ℕ)
    (gl gh U : ℚ) : ℚ := ∑ k, boxTerm (a k) (b k) gl gh U (ix k) (iy k)
noncomputable def boxPolynomial {ι : Type*} [Fintype ι] (a b : ι → ℚ) (ix iy : ι → ℕ)
    (g x y : ℝ) : ℝ := ∑ k, ((a k:ℝ)+(b k:ℝ)*g)*x^(ix k)*y^(iy k)

theorem boxTerm_lower (a b gl gh U : ℚ) (i j : ℕ) (g x y : ℝ)
    (hglo : (gl:ℝ) ≤ g) (hghi : g ≤ (gh:ℝ))
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hX : x ≤ (U:ℝ)) (hY : y ≤ (U:ℝ)) :
    (boxTerm a b gl gh U i j:ℝ) ≤ ((a:ℝ)+(b:ℝ)*g)*x^i*y^j := by
  have hc : (intervalCoefficient a b gl gh:ℝ) ≤ (a:ℝ)+(b:ℝ)*g :=
    rational_affine_interval a b gl gh g hglo hghi
  unfold boxTerm
  split_ifs with hz
  · have hi : i=0 := by omega
    have hj : j=0 := by omega
    simpa [hi,hj] using hc
  · have xp := nonnegative_power_bounds x (U:ℝ) hx hX i
    have yp := nonnegative_power_bounds y (U:ℝ) hy hY j
    have hu : (0:ℝ) ≤ U := hx.trans hX
    have hp : x^i*y^j ≤ (U:ℝ)^i*(U:ℝ)^j :=
      mul_le_mul xp.2 yp.2 yp.1 (pow_nonneg hu i)
    have h := monomial_lower ((a:ℝ)+(b:ℝ)*g) (intervalCoefficient a b gl gh:ℝ)
      (x^i*y^j) ((U:ℝ)^i*(U:ℝ)^j) hc (mul_nonneg xp.1 yp.1) hp
    simpa only [Rat.cast_min, Rat.cast_zero, Rat.cast_mul, Rat.cast_pow, mul_assoc] using h

/-- Any finite affine-coefficient polynomial has a computable exact-rational lower envelope on a box. -/
theorem boxEnvelope_lower {ι : Type*} [Fintype ι]
    (a b : ι → ℚ) (ix iy : ι → ℕ) (gl gh U : ℚ) (g x y : ℝ)
    (hglo : (gl:ℝ) ≤ g) (hghi : g ≤ (gh:ℝ))
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hX : x ≤ (U:ℝ)) (hY : y ≤ (U:ℝ)) :
    (boxEnvelope a b ix iy gl gh U:ℝ) ≤ boxPolynomial a b ix iy g x y := by
  unfold boxEnvelope boxPolynomial
  push_cast
  exact Finset.sum_le_sum fun k _ => boxTerm_lower (a k) (b k) gl gh U (ix k) (iy k)
    g x y hglo hghi hx hy hX hY
end SparseComponent.TotalFamily
