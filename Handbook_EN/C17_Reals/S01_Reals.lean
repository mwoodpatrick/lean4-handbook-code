/- Chapter 17: Real numbers and limits of sequences
   17.1 What are the real numbers? -- a complete ordered field
   17.2 Suprema and infima -/
import Mathlib

namespace Handbook.C17

-- BOOK: begin reals-lub
-- The heart of ℝ: a nonempty set bounded above has a supremum
-- (a least upper bound)
example (S : Set ℝ) (hne : S.Nonempty) (hbdd : BddAbove S) :
    IsLUB S (sSup S) :=
  isLUB_csSup hne hbdd
-- BOOK: end reals-lub

-- BOOK: begin reals-sqrt2
-- so √2 "exists" (it did not exist in ℚ: Chapter 6)
example : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
-- BOOK: end reals-sqrt2

-- BOOK: begin reals-arch
-- The Archimedean property: some natural number exceeds any given real
example (x : ℝ) : ∃ n : ℕ, x < n := exists_nat_gt x

-- ℝ is an Archimedean ordered field (already registered as an instance)
example : Archimedean ℝ := inferInstance
-- BOOK: end reals-arch

-- BOOK: begin reals-sup-lemmas
-- The supremum is the least upper bound: two lemmas give
-- the two sides
example (S : Set ℝ) (x : ℝ) (hbdd : BddAbove S) (hx : x ∈ S) :
    x ≤ sSup S :=
  le_csSup hbdd hx

example (S : Set ℝ) (hne : S.Nonempty) (b : ℝ)
    (hb : ∀ x ∈ S, x ≤ b) : sSup S ≤ b :=
  csSup_le hne hb
-- BOOK: end reals-sup-lemmas

end Handbook.C17
