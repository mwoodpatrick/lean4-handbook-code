/- English edition source: Handbook/C18_Continuity/S01_Continuity.lean. -/
import Mathlib

namespace Handbook.C18

open Topology

-- BOOK: begin cont-epsdelta
-- The definition of continuity is equivalent to ε-δ (a translation
-- theorem)
example (f : ℝ → ℝ) (a : ℝ) :
    ContinuousAt f a ↔
      ∀ ε > 0, ∃ δ > 0, ∀ x, |x - a| < δ → |f x - f a| < ε := by
  rw [Metric.continuousAt_iff]
  simp [Real.dist_eq]
-- BOOK: end cont-epsdelta

-- BOOK: begin cont-auto
-- fun_prop automatically assembles continuity proofs for concrete
-- functions
example : Continuous (fun x : ℝ => x ^ 2 + 3 * x) := by fun_prop

example : Continuous (fun x : ℝ => Real.sin (x ^ 2)) := by fun_prop
-- BOOK: end cont-auto

-- BOOK: begin cont-comp
-- Compositions, sums, and products of continuous functions are
-- continuous (assembled by hand)
example (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => f (g x)) :=
  hf.comp hg

example (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => f x + g x) :=
  hf.add hg
-- BOOK: end cont-comp

-- BOOK: begin cont-limit
-- Continuity at a means “as x → a, f x → f a” (limit = function value)
example (f : ℝ → ℝ) (a : ℝ) (hf : ContinuousAt f a) :
    Filter.Tendsto f (𝓝 a) (𝓝 (f a)) :=
  hf.tendsto
-- BOOK: end cont-limit

end Handbook.C18
