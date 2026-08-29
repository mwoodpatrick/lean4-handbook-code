/- English edition source: Handbook/C11_ExpLog/S01_PowLaws.lean. -/
import Mathlib

namespace Handbook.C11

-- BOOK: begin pow-laws
-- Laws of exponents (natural-number powers)
example (a : ℚ) (m n : ℕ) : a ^ (m + n) = a ^ m * a ^ n :=
  pow_add a m n

example (a : ℚ) (m n : ℕ) : (a ^ m) ^ n = a ^ (m * n) :=
  (pow_mul a m n).symm
-- BOOK: end pow-laws

-- BOOK: begin pow-zpow
-- Integer powers (zpow): a negative exponent means a reciprocal
example (a : ℚ) : a ^ (-1 : ℤ) = a⁻¹ := zpow_neg_one a

example (a : ℚ) : a ^ (0 : ℤ) = 1 := zpow_zero a
-- BOOK: end pow-zpow

end Handbook.C11
