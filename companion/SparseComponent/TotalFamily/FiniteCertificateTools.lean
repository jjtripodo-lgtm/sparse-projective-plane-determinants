import SparseComponent.TotalFamily.PolynomialTools
import Mathlib.Data.Rat.Cast.Order

namespace SparseComponent.TotalFamily
open Real

theorem affine_min_interval (a b gl g gh : ℝ) (hlo : gl ≤ g) (hhi : g ≤ gh) :
    min (a+b*gl) (a+b*gh) ≤ a+b*g := by
  by_cases hb : 0 ≤ b
  · exact (min_le_left _ _).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hlo hb))
  · exact (min_le_right _ _).trans (add_le_add le_rfl (mul_le_mul_of_nonpos_left hhi (le_of_not_ge hb)))

theorem rational_affine_interval (a b gl gh : ℚ) (g : ℝ)
    (hlo : (gl:ℝ) ≤ g) (hhi : g ≤ (gh:ℝ)) :
    ((min (a+b*gl) (a+b*gh):ℚ):ℝ) ≤ (a:ℝ)+(b:ℝ)*g := by
  push_cast
  exact affine_min_interval a b gl g gh hlo hhi

/-- Exact-rational finite certificate gate, with every analytic enclosure explicit. -/
theorem rational_edge_gate (a b gl gh x y lx ly : ℚ) (g X Y : ℝ)
    (hx0 : 0 ≤ x) (hy0 : 0 ≤ y)
    (hglo : (gl:ℝ) ≤ g) (hghi : g ≤ (gh:ℝ))
    (hX : (lx:ℝ) ≤ X) (hY : (ly:ℝ) ≤ Y)
    (hgate : 0 < min (a+b*gl) (a+b*gh)+x*lx+y*ly) :
    0 < (a:ℝ)+(b:ℝ)*g+(x:ℝ)*X+(y:ℝ)*Y := by
  have hg := rational_affine_interval a b gl gh g hglo hghi
  have hx := mul_le_mul_of_nonneg_left hX (show (0:ℝ) ≤ x by exact_mod_cast hx0)
  have hy := mul_le_mul_of_nonneg_left hY (show (0:ℝ) ≤ y by exact_mod_cast hy0)
  have hb : (0:ℝ) < ((min (a+b*gl) (a+b*gh):ℚ):ℝ)+(x:ℝ)*(lx:ℝ)+(y:ℝ)*(ly:ℝ) := by
    exact_mod_cast hgate
  exact lt_of_lt_of_le hb (add_le_add (add_le_add hg hx) hy)
end SparseComponent.TotalFamily
