/- English edition source: Handbook/C25_ODE/S01_ODE.lean. -/
import Mathlib

namespace Handbook.C25

-- BOOK: begin ode-verify
-- Guess and verify: x(t) = C·eᵗ satisfies x' = x
example (C : ℝ) (t : ℝ) :
    HasDerivAt (fun s => C * Real.exp s) (C * Real.exp t) t := by
  simpa using (Real.hasDerivAt_exp t).const_mul C
-- BOOK: end ode-verify

-- BOOK: begin ode-def
-- "x solves ẋ = f(t,x)" is written with the predicates of
-- Chapter 19 alone; no new definition is introduced
def IsSolution (f : ℝ → ℝ → ℝ) (x : ℝ → ℝ) : Prop :=
  ∀ t, HasDerivAt x (f t (x t)) t

-- the computation above fits the shape of this predicate
example (C : ℝ) : IsSolution (fun _ x => x) (fun s => C * Real.exp s) :=
  fun t => by simpa using (Real.hasDerivAt_exp t).const_mul C
-- BOOK: end ode-def

end Handbook.C25
