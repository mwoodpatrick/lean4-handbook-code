/- English edition source: Handbook/C24_Multivar/S03_Chain.lean. -/
import Mathlib

namespace Handbook.C24

-- BOOK: begin chain-sum
-- The total derivative of a sum is the sum of the total derivatives
-- (added as linear maps)
example (f g : ℝ × ℝ → ℝ) (f' g' : ℝ × ℝ →L[ℝ] ℝ) (x : ℝ × ℝ)
    (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) :
    HasFDerivAt (f + g) (f' + g') x :=
  hf.add hg
-- BOOK: end chain-sum

-- BOOK: begin chain-curve
-- Follow f along the curve s ↦ (s, s²).
-- The rate of change is the linear approximation of f applied to
-- the velocity vector.
example (f : ℝ × ℝ → ℝ) (f' : ℝ × ℝ →L[ℝ] ℝ) (t : ℝ)
    (hf : HasFDerivAt f f' (t, t ^ 2)) :
    HasDerivAt (fun s : ℝ => f (s, s ^ 2)) (f' (1, 2 * t)) t := by
  have hg : HasDerivAt (fun s : ℝ => (s, s ^ 2)) (1, 2 * t) t := by
    simpa using (hasDerivAt_id t).prodMk (hasDerivAt_pow 2 t)
  exact hf.comp_hasDerivAt t hg
-- BOOK: end chain-curve

-- BOOK: begin chain-unique
-- The total derivative is unique, so the Jacobian matrix is
-- well defined
example (f : ℝ × ℝ → ℝ) (f' g' : ℝ × ℝ →L[ℝ] ℝ) (x : ℝ × ℝ)
    (h1 : HasFDerivAt f f' x) (h2 : HasFDerivAt f g' x) : f' = g' :=
  h1.unique h2

-- having a total derivative implies continuity
example (f : ℝ × ℝ → ℝ) (f' : ℝ × ℝ →L[ℝ] ℝ) (x : ℝ × ℝ)
    (h : HasFDerivAt f f' x) : ContinuousAt f x :=
  h.continuousAt
-- BOOK: end chain-unique

end Handbook.C24
