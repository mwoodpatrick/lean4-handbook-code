/- English edition source: Handbook/C41_Automation/S02_Decide.lean. -/
import Mathlib

namespace Handbook.C41

-- BOOK: begin decide
-- decide: settle a finite case by exhaustive check
example : (2 : ℤ) ^ 10 = 1024 := by decide
example : ∀ a b : ZMod 4, a ^ 2 + b ^ 2 ≠ 3 := by decide
example : Nat.Prime 97 := by decide
-- BOOK: end decide

-- BOOK: begin omega
-- omega: decides linear integer arithmetic, including the truncated
-- subtraction of ℕ
example (n : ℕ) : n % 3 < 3 := by omega
example (a b : ℤ) (h : 2 * a + 3 * b = 7) (h2 : a = 2) : b = 1 := by
  omega
example (n : ℕ) (h : 0 < n) : n - 1 + 1 = n := by omega
-- BOOK: end omega

-- BOOK: begin norm-num
-- norm_num: normalizes numerical calculations; it is broader and faster
-- than decide for arithmetic.
example : (123 : ℝ) * 456 = 56088 := by norm_num
example : (7 : ℚ) / 2 > 3 := by norm_num
example : Nat.Prime 1000003 := by norm_num
-- BOOK: end norm-num

end Handbook.C41
