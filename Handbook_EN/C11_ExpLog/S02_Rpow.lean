/- English edition source: Handbook/C11_ExpLog/S02_Rpow.lean. -/
import Mathlib

namespace Handbook.C11

-- BOOK: begin rpow-three
-- The same ^ notation denotes different operations depending on the
-- exponent type
#check (2 : ℝ) ^ (3 : ℕ)    -- natural-number power (npow)
#check (2 : ℝ) ^ (-3 : ℤ)   -- integer power (zpow)
#check (2 : ℝ) ^ (0.5 : ℝ)  -- real power (Real.rpow)
-- BOOK: end rpow-three

-- BOOK: begin rpow-sqrt
-- A square root is a power of 1/2
example (x : ℝ) : Real.sqrt x = x ^ (1 / 2 : ℝ) :=
  Real.sqrt_eq_rpow x
-- BOOK: end rpow-sqrt

-- BOOK: begin rpow-twelfth
-- Stacking the semitone 2^(1/12) twelve times gives exactly a factor of
-- two (an octave)
example : ((2 : ℝ) ^ ((1 : ℝ) / 12)) ^ (12 : ℕ) = 2 := by
  rw [← Real.rpow_natCast ((2 : ℝ) ^ ((1 : ℝ) / 12)) 12,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    show (1 : ℝ) / 12 * ((12 : ℕ) : ℝ) = 1 by
      push_cast; norm_num,
    Real.rpow_one]
-- BOOK: end rpow-twelfth

end Handbook.C11
