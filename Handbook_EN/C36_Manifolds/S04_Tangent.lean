/- Chapter 36: Manifolds
   36.4 Tangent spaces and differentiation on manifolds -/
import Mathlib

open Manifold

namespace Handbook.C36

-- BOOK: begin tangent-space
-- The tangent space: a vector space attached at each point
#check @TangentSpace
-- the tangent bundle: all the tangent spaces bundled into a manifold
#check @TangentBundle
-- BOOK: end tangent-space

-- BOOK: begin mfderiv
-- Differentiation on a manifold; the manifold version of the fderiv
-- of Chapter 19
#check @mfderiv
-- over ℝ it agrees with the ordinary derivative
example (f : ℝ → ℝ) (x : ℝ) :
    mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ)
      f x = fderiv ℝ f x := by
  rw [mfderiv_eq_fderiv]
-- BOOK: end mfderiv

end Handbook.C36
