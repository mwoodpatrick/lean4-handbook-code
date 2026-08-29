/- English edition source: Handbook/C16_Sets/S07_InjSurj.lean. -/
import Mathlib

namespace Handbook.C16

-- BOOK: begin injsurj-def
-- Injective: equal outputs imply equal inputs; the map “collapses
-- nothing”
example (f : ℕ → ℕ) (hf : Function.Injective f) (a b : ℕ)
    (h : f a = f b) : a = b := hf h

-- Surjective: every output is someone’s image; the map “misses nothing”
#check @Function.Surjective

-- A bijection is both
#check @Function.Bijective
-- BOOK: end injsurj-def

-- BOOK: begin injsurj-example
-- n ↦ n + 1 is injective
example : Function.Injective (fun n : ℕ => n + 1) := by
  intro a b h
  simpa using h

-- But it is not surjective: 0 is not the image of anything
example : ¬ Function.Surjective (fun n : ℕ => n + 1) := by
  intro h
  obtain ⟨a, ha⟩ := h 0
  simp at ha
-- BOOK: end injsurj-example

-- BOOK: begin inverse
-- Being bijective is equivalent to having a two-sided inverse
example (f : ℕ → ℕ) (hf : Function.Bijective f) :
    ∃ g, Function.LeftInverse g f ∧ Function.RightInverse g f :=
  Function.bijective_iff_has_inverse.mp hf

-- From an injection we can build a left inverse invFun (assuming a
-- nonempty domain)
#check @Function.leftInverse_invFun
-- BOOK: end inverse

-- BOOK: begin comp-inj
-- A composition of injections is injective; likewise for surjections
#check @Function.Injective.comp
#check @Function.Surjective.comp

-- If f is injective, f a = f b can be converted to a = b
#check @Function.Injective.eq_iff
-- BOOK: end comp-inj

-- BOOK: begin comp-inj-inner
-- If g ∘ f is injective then f is injective: apply g to both sides of
-- f a = f b and use the injectivity of the composition
example (f g : ℕ → ℕ) (h : Function.Injective (g ∘ f)) :
    Function.Injective f := by
  intro a b hab
  exact h (congrArg g hab)

-- mathlib records the same fact as Function.Injective.of_comp
example (f g : ℕ → ℕ) (h : Function.Injective (g ∘ f)) :
    Function.Injective f :=
  h.of_comp
-- BOOK: end comp-inj-inner

end Handbook.C16
