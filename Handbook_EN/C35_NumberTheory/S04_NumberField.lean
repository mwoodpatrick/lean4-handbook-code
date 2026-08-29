/- English edition source: Handbook/C35_NumberTheory/S04_NumberField.lean. -/
import Mathlib

namespace Handbook.C35

-- BOOK: begin number-field
-- A number field is a finite extension of ℚ; ℚ itself is the smallest
-- example.
#check @NumberField

-- Its ring of integers; for ℚ this is ℤ
#check @NumberField.RingOfIntegers
-- BOOK: end number-field

-- BOOK: begin algebraic-int
-- An algebraic integer is a root of a monic polynomial with integer
-- coefficients; √2 is an example.
example : IsIntegral ℤ (Real.sqrt 2) := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C 2, ?_, ?_⟩
  · exact Polynomial.monic_X_pow_sub_C 2 (by norm_num)
  · simp

-- 1/2 is algebraic but not an algebraic integer (a denominator
-- remains)
example : IsIntegral ℚ ((1 : ℚ) / 2) :=
  isIntegral_algebraMap
-- BOOK: end algebraic-int

-- BOOK: begin class-group
-- The ideal class group measures how far unique factorization fails
#check @ClassGroup

-- for the ring of integers of a number field it is finite
-- (the class number)
#check @ClassGroup.fintypeOfAdmissibleOfFinite
-- BOOK: end class-group

end Handbook.C35
