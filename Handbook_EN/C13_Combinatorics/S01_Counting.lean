/- English edition source: Handbook/C13_Combinatorics/S01_Counting.lean. -/
import Mathlib

namespace Handbook.C13

open Finset

-- BOOK: begin count-card
#eval (range 10).card  -- output: 10

-- Product rule: the cardinality of a Cartesian product is the product
-- of the cardinalities
example (s t : Finset ℕ) : (s ×ˢ t).card = s.card * t.card :=
  Finset.card_product s t

-- Sum rule: the cardinality of a disjoint union is the sum of the
-- cardinalities
example (s t : Finset ℕ) (h : Disjoint s t) :
    (s ∪ t).card = s.card + t.card :=
  Finset.card_union_of_disjoint h
-- BOOK: end count-card

-- BOOK: begin count-concrete
-- Three Japanese sweets and four Western sweets: 7 ways to choose one,
-- 12 ways to choose one of each
#eval (range 3 ∪ (range 7 \ range 3)).card       -- output: 7
#eval ((range 3) ×ˢ (range 4)).card              -- output: 12

-- Three shirts × two pairs of trousers = six outfits: the product rule
-- in action.
example : ((range 3) ×ˢ (range 2)).card = 6 := by decide
-- BOOK: end count-concrete

end Handbook.C13
