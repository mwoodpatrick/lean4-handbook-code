/- English edition source: Handbook/C19_Derivatives/S01_Deriv.lean. -/
import Mathlib

namespace Handbook.C19

-- BOOK: begin deriv-def
-- HasDerivAt f c x: f has derivative c at x
example : HasDerivAt (fun x : ℝ => x ^ 2) 6 3 := by
  have h := hasDerivAt_pow 2 (3 : ℝ)
  norm_num at h
  exact h

-- deriv is “the function that returns the derivative”
example : deriv (fun x : ℝ => x ^ 2) 3 = 6 := by
  norm_num [deriv_pow]
-- BOOK: end deriv-def

-- BOOK: begin deriv-rules
-- Product rule (Leibniz rule)
example (f g : ℝ → ℝ) (x : ℝ)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    deriv (fun y => f y * g y) x
      = deriv f x * g x + f x * deriv g x :=
  deriv_mul hf hg

-- Chain rule (derivative of a composition)
example (f g : ℝ → ℝ) (x : ℝ)
    (hg : DifferentiableAt ℝ g x)
    (hf : DifferentiableAt ℝ f (g x)) :
    deriv (f ∘ g) x = deriv f (g x) * deriv g x :=
  deriv_comp x hf hg
-- BOOK: end deriv-rules

-- BOOK: begin deriv-basic
-- Basic derivative formulas (constant, identity, power)
example (c : ℝ) : deriv (fun _ : ℝ => c) = fun _ => 0 := by
  funext x; simp

example : deriv (fun x : ℝ => x) = fun _ => 1 := by
  funext x; simp

-- (xⁿ)' = n xⁿ⁻¹
example (n : ℕ) (x : ℝ) :
    deriv (fun y : ℝ => y ^ n) x = n * x ^ (n - 1) := by
  simp
-- BOOK: end deriv-basic

-- BOOK: begin deriv-add
-- The derivative of a sum is the sum of the derivatives
example (f g : ℝ → ℝ) (x : ℝ)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    deriv (fun y => f y + g y) x = deriv f x + deriv g x :=
  deriv_add hf hg
-- BOOK: end deriv-add

end Handbook.C19
