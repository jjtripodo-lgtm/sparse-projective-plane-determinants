import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Tactic.Linarith

namespace SparseComponent
open Set

/-- Rolle on a positive interval, using an explicit derivative function. -/
theorem positive_rolle {f f' : ℝ → ℝ} (h : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (heq : f a = f b) :
    ∃ c, a < c ∧ c < b ∧ f' c = 0 := by
  obtain ⟨c, hc, hzero⟩ := exists_hasDerivAt_eq_zero hab
    (fun x hx => (h x (lt_of_lt_of_le ha hx.1)).continuousAt.continuousWithinAt)
    heq (fun x hx => h x (lt_trans ha hx.1))
  exact ⟨c, hc.1, hc.2, hzero⟩

/-- Three Rolle steps for one double interpolation node and two simple nodes. -/
theorem hermite_third_derivative_zero
    {f f' f'' f''' : ℝ → ℝ}
    (h0 : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (h1 : ∀ x, 0 < x → HasDerivAt f' (f'' x) x)
    (h2 : ∀ x, 0 < x → HasDerivAt f'' (f''' x) x)
    {t R x : ℝ} (ht : 0 < t) (htR : t < R) (hx : 0 < x) (hxR : x < R)
    (hxt : x ≠ t) (hft : f t = 0) (hfR : f R = 0) (hfx : f x = 0)
    (hf't : f' t = 0) : ∃ ξ, 0 < ξ ∧ ξ < R ∧ f''' ξ = 0 := by
  rcases lt_or_gt_of_ne hxt with hxt | htx
  · obtain ⟨a, hxa, hat, hfa⟩ := positive_rolle h0 hx hxt (hfx.trans hft.symm)
    obtain ⟨b, htb, hbR, hfb⟩ := positive_rolle h0 ht htR (hft.trans hfR.symm)
    obtain ⟨c, hac, hct, hfc⟩ := positive_rolle h1 (hx.trans hxa) hat (hfa.trans hf't.symm)
    obtain ⟨d, htd, hdb, hfd⟩ := positive_rolle h1 ht htb (hf't.trans hfb.symm)
    obtain ⟨ξ, hcξ, hξd, hfξ⟩ := positive_rolle h2 (by linarith) (by linarith) (hfc.trans hfd.symm)
    exact ⟨ξ, by linarith, by linarith, hfξ⟩
  · obtain ⟨a, hta, hax, hfa⟩ := positive_rolle h0 ht htx (hft.trans hfx.symm)
    obtain ⟨b, hxb, hbR, hfb⟩ := positive_rolle h0 hx hxR (hfx.trans hfR.symm)
    obtain ⟨c, htc, hca, hfc⟩ := positive_rolle h1 ht hta (hf't.trans hfa.symm)
    obtain ⟨d, had, hdb, hfd⟩ := positive_rolle h1 (ht.trans hta) (by linarith) (hfa.trans hfb.symm)
    obtain ⟨ξ, hcξ, hξd, hfξ⟩ := positive_rolle h2 (ht.trans htc) (by linarith) (hfc.trans hfd.symm)
    exact ⟨ξ, by linarith, by linarith, hfξ⟩

end SparseComponent
