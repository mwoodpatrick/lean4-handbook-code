/- English edition source: Handbook/C19_Derivatives/S05_Applications.lean. -/
import Mathlib

namespace Handbook.C19

-- BOOK: begin local-extr
-- Fermat’s theorem: the derivative vanishes at a local minimum
example (f : ℝ → ℝ) (a : ℝ) (h : IsLocalMin f a) :
    deriv f a = 0 :=
  h.deriv_eq_zero

-- There is also an IsLocalExtr version combining maxima and minima
#check @IsLocalExtr.deriv_eq_zero
-- BOOK: end local-extr

-- BOOK: begin rolle-search
-- A deriv version of Rolle’s theorem, yielding a stationary point
#check @exists_deriv_eq_zero
-- BOOK: end rolle-search

-- BOOK: begin inv-deriv
-- Derivative of an inverse. log is the inverse of exp, and (log)' x =
-- 1/x
example (x : ℝ) (hx : x ≠ 0) : HasDerivAt Real.log x⁻¹ x :=
  Real.hasDerivAt_log hx

-- General form. It requires f' ≠ 0 (a horizontal tangent prevents
-- differentiability of the inverse)
#check @HasDerivAt.of_local_left_inverse
-- BOOK: end inv-deriv

-- BOOK: begin convex-deriv2
-- A positive second derivative implies strict convexity; verify this
-- for x ↦ x²
example : StrictConvexOn ℝ Set.univ (fun x : ℝ => x ^ 2) := by
  apply strictConvexOn_of_deriv2_pos convex_univ
  · fun_prop
  · intro x _
    simp
    norm_num
-- BOOK: end convex-deriv2

-- BOOK: begin contdiff-inf
-- exp is C^∞. Since n : WithTop ℕ∞, the statement holds for every
-- order.
#check @Real.contDiff_exp

-- Characterization of C^∞: differentiable with a derivative that is
-- itself C^∞
#check @contDiff_infty_iff_deriv
-- BOOK: end contdiff-inf

end Handbook.C19
