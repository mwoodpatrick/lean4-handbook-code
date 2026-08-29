/- Chapter 8: The basics of functions
   8.6 Composition and commutative diagrams -/
import Mathlib

namespace Handbook.C08

-- BOOK: begin comp-noncomm
-- Composition is sensitive to order:
-- "double then add one" differs from "add one then double"
#eval (fun x : ℚ => 2 * x + 1) 5     -- output: 11
#eval (fun x : ℚ => 2 * (x + 1)) 5   -- output: 12

example : ∃ x : ℚ, 2 * x + 1 ≠ 2 * (x + 1) :=
  ⟨0, by norm_num⟩
-- BOOK: end comp-noncomm

-- BOOK: begin comp-def
-- The composition g ∘ f. A composition of injections is injective.
example (f g : ℚ → ℚ) (hf : Function.Injective f)
    (hg : Function.Injective g) :
    Function.Injective (g ∘ f) :=
  hg.comp hf

-- A composition of surjections is surjective
example (f g : ℚ → ℚ) (hf : Function.Surjective f)
    (hg : Function.Surjective g) :
    Function.Surjective (g ∘ f) :=
  hg.comp hf
-- BOOK: end comp-def

-- BOOK: begin comp-assoc
-- Composition is associative; the ground for commutative diagrams
example (f g h : ℚ → ℚ) : (h ∘ g) ∘ f = h ∘ (g ∘ f) :=
  Function.comp_assoc h g f
-- BOOK: end comp-assoc

-- BOOK: begin functions-exercises
-- Exercises: injectivity, a value, and a property of composition
example : Function.Injective (fun x : ℚ => x - 4) := by
  intro a b h
  dsimp only at h
  linarith

example : (fun x : ℚ => x ^ 2 + 1) 3 = 10 := by norm_num

example (f : ℚ → ℚ) (hf : Function.Injective f) :
    Function.Injective (f ∘ f) :=
  hf.comp hf
-- BOOK: end functions-exercises

end Handbook.C08
