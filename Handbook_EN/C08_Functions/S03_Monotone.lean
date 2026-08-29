/- Chapter 8: The basics of functions
   8.4 Monotonicity -/
import Mathlib

namespace Handbook.C08

-- BOOK: begin mono-def
-- A proof of strict monotonicity straight from the definition
example : StrictMono (fun x : ℚ => 2 * x + 1) := by
  intro a b hab
  dsimp only
  linarith
-- BOOK: end mono-def

-- BOOK: begin mono-inj
-- A strictly monotone function is injective
-- (the order forbids a collision of values)
example (f : ℚ → ℚ) (hf : StrictMono f) :
    Function.Injective f :=
  hf.injective
-- BOOK: end mono-inj

-- BOOK: begin mono-comp
-- A composition of monotone functions is monotone
example (f g : ℚ → ℚ) (hf : StrictMono f) (hg : StrictMono g) :
    StrictMono (g ∘ f) :=
  hg.comp hf
-- BOOK: end mono-comp

-- BOOK: begin fun-seq
-- A sequence is nothing but a function out of ℕ (Chapter 12 revisited)
def seq (n : ℕ) : ℚ := n ^ 2

#eval [seq 0, seq 1, seq 2, seq 3]    -- output: [0, 1, 4, 9]
-- BOOK: end fun-seq

end Handbook.C08
