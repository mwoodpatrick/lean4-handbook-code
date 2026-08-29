/- English edition source: Handbook/C14_Integers/S07_CRT.lean. -/
import Mathlib

namespace Handbook.C14

-- BOOK: begin crt-example
-- A number congruent to 2 modulo 3 and 3 modulo 5 is uniquely 8 modulo
-- 15
example : (8 : ℕ) % 3 = 2 ∧ (8 : ℕ) % 5 = 3 := by decide

-- Below 15, only 8 satisfies those conditions
example : ∀ n < 15, n % 3 = 2 ∧ n % 5 = 3 → n = 8 := by decide
-- BOOK: end crt-example

-- BOOK: begin crt-equiv
-- General form: decomposition into coprime moduli gives a ring
-- isomorphism
#check @ZMod.chineseRemainder

-- ℤ/(3·5) ≃ ℤ/3 × ℤ/5. The left side must be written in product form.
noncomputable example :
    ZMod (3 * 5) ≃+* ZMod 3 × ZMod 5 :=
  ZMod.chineseRemainder (by norm_num)
-- BOOK: end crt-equiv

-- BOOK: begin crt-coprime
-- It fails without coprimality: ℤ/4 is not isomorphic to ℤ/2 × ℤ/2
-- (the left has an element of order 4, while the right does not)
example : ((2 : ZMod 4) + 2) = 0 := by decide

example : ∀ x : ZMod 2 × ZMod 2, x + x = 0 := by decide
-- BOOK: end crt-coprime

end Handbook.C14
