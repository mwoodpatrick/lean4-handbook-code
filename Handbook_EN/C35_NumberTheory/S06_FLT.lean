/- English edition source: Handbook/C35_NumberTheory/S06_FLT.lean. -/
import Mathlib

namespace Handbook.C35

-- BOOK: begin flt-statement
-- The statement of Fermat's last theorem: for n ≥ 3 there is no
-- non-trivial solution
#check @FermatLastTheorem

-- the version with the exponent n fixed
#check @FermatLastTheoremFor
-- BOOK: end flt-statement

-- BOOK: begin flt-four
-- The case n = 4, which Fermat himself proved by infinite descent
example : FermatLastTheoremFor 4 :=
  fermatLastTheoremFour

-- The case n = 3, due to Euler (1770), is formalized in mathlib too
example : FermatLastTheoremFor 3 :=
  fermatLastTheoremThree
-- BOOK: end flt-four

-- BOOK: begin pythagorean
-- For n = 2 there are infinitely many solutions (Pythagorean triples)
example : 3 ^ 2 + 4 ^ 2 = 5 ^ 2 := by norm_num
example : 5 ^ 2 + 12 ^ 2 = 13 ^ 2 := by norm_num
example : 8 ^ 2 + 15 ^ 2 = 17 ^ 2 := by norm_num

-- the general form (m²−k²)² + (2mk)² = (m²+k²)²
example (m k : ℤ) :
    (m ^ 2 - k ^ 2) ^ 2 + (2 * m * k) ^ 2 = (m ^ 2 + k ^ 2) ^ 2 := by
  ring
-- BOOK: end pythagorean

end Handbook.C35
