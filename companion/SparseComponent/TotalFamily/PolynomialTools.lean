import SparseComponent.TotalFamily.LinearTools
import SparseComponent.TotalFamily.AllCertificates

namespace SparseComponent.TotalFamily
open Real

noncomputable def polynomialModel (r : ℝ) (anchor : ℝ → ℝ) (x y : ℝ) : ℝ :=
  2/r-1/(r-1)+(x+y)/(r-1)-r^2/(r-1)*x*y + gamma r*(
    2*r-1-r^2*(x+y)-2*r^2*(r-1)*x*y +
    r^4*(-x*(anchor x)^2-y*(anchor y)^2 +
      2*x*y*(anchor x+anchor y)-(x^3*y+x*y^3)/2))

/-- The polynomial/entropy split is valid for every anchor, including the quadratic and cubic ones. -/
theorem polynomial_edge_identity (r x y : ℝ) (hr : 2 ≤ r) (anchor : ℝ → ℝ) :
    edgePolynomial r anchor x y + edgePolynomial r anchor y x =
      polynomialModel r anchor x y + x*log (r*x)+y*log (r*y) := by
  simp only [edgePolynomial, baseValue_explicit r hr, slope, balance, logB, polynomialModel]
  have hr0 : r ≠ 0 := by linarith
  have ht : r-1 ≠ 0 := by linarith
  simp only [gamma]
  field_simp [hr0, ht]
  ring
end SparseComponent.TotalFamily
