import SparseComponent.TotalFamily.Edge

namespace SparseComponent.TotalFamily
open Real

noncomputable def linearAnchor (r x : ℝ) : ℝ := 2/(5*r)+3*x/5
noncomputable def quadraticAnchor (x : ℝ) : ℝ := -1/100+6*x/5-x^2
noncomputable def cubicAnchor (r x : ℝ) : ℝ := x-(2/3)*(x-1/r)^2-(3/2)*(x-1/r)^3

theorem linearAnchor_plane (r : ℝ) (hr : r ≠ 0) : linearAnchor r (1/r) = 1/r := by
  unfold linearAnchor
  field_simp
  ring

theorem quadraticAnchor_plane : quadraticAnchor (1/10) = 1/10 := by
  norm_num [quadraticAnchor]

theorem cubicAnchor_plane (r : ℝ) : cubicAnchor r (1/r) = 1/r := by
  simp [cubicAnchor]

/-- The written source's nonsingular polynomial-plus-log expression for one directed edge. -/
noncomputable def edgePolynomial (r : ℝ) (anchor : ℝ → ℝ) (x y : ℝ) : ℝ :=
  let a := anchor x
  let L := logB (r-1) (r^2)*r^2/2 + r^4*gamma r*x^2/2
  x*baseValue r + slope r*(1-r*x) + balance r*(a-x) - x*L*a +
    x*r^4*gamma r*a^2 + x*log (r*x) +
    (balance r-x*L+2*x*r^4*gamma r*a)*(y-a)

/-- Exact binding of the matrix-edge expression to the scalar certificate expression. -/
theorem edgeForward_reciprocal (r x y : ℝ) (hr : r ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0)
    (anchor : ℝ → ℝ) :
    edgeForward r anchor (1/x) (1/y) = edgePolynomial r anchor x y := by
  have hl : log ((1/x)/r) = -log (r*x) := by
    rw [show (1/x)/r = (r*x)⁻¹ by ring, log_inv]
  simp only [edgeForward, one_div_one_div, deficit, deficitDerivative, vertex, hl, edgePolynomial]
  field_simp
  ring

theorem edgeCost_reciprocal (r x y : ℝ) (hr : r ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0)
    (anchor : ℝ → ℝ) :
    edgeCost r anchor (1/x) (1/y) =
      edgePolynomial r anchor x y + edgePolynomial r anchor y x := by
  unfold edgeCost
  rw [edgeForward_reciprocal r x y hr hx hy, edgeForward_reciprocal r y x hr hy hx]

/-- A certificate in the exact reciprocal-variable format suffices for the matrix bridge. -/
theorem certificate_of_reciprocal (r : ℝ) (hr : r ≠ 0) (K : ℤ) (hK : 0 ≤ K)
    (anchor : ℝ → ℝ)
    (hcert : ∀ d c : ℤ, K < d → K < c →
      0 ≤ edgePolynomial r anchor (1/(d:ℝ)) (1/(c:ℝ)) +
        edgePolynomial r anchor (1/(c:ℝ)) (1/(d:ℝ))) :
    EdgeCertificate r K anchor := by
  intro d c hd hc
  have hdp : (d:ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_le_of_lt hK hd))
  have hcp : (c:ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_le_of_lt hK hc))
  have he := edgeCost_reciprocal r (1/(d:ℝ)) (1/(c:ℝ)) hr (one_div_ne_zero hdp)
    (one_div_ne_zero hcp) anchor
  simp only [one_div_one_div] at he
  rw [he]
  exact hcert d c hd hc
end SparseComponent.TotalFamily
