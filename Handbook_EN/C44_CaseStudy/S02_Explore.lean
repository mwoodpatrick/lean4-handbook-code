/- Chapter 44: Case study -- formalizing one theorem
   44.2 Exploring and checking -/
import Handbook_EN.C44_CaseStudy.S01_Nicomachus

namespace Handbook.C44

open Finset

-- BOOK: begin explore-eval
-- First check it numerically: the stage of doubting the claim
#eval (List.range 6).map fun n =>
  (∑ k ∈ range (n + 1), k ^ 3, (∑ k ∈ range (n + 1), k) ^ 2)
-- BOOK: end explore-eval

-- BOOK: begin explore-closed
-- The closed form of Gauss's sum, from 2S = n(n+1) of Chapter 12
theorem sum_range_closed (n : ℕ) :
    2 * ∑ k ∈ range (n + 1), k = n * (n + 1) :=
  Handbook.C12.gauss_sum n
-- BOOK: end explore-closed

-- BOOK: begin explore-axioms
-- Confirm that the proof does not depend on sorry
#print axioms nicomachus
#print axioms sum_range_closed
-- BOOK: end explore-axioms

end Handbook.C44
