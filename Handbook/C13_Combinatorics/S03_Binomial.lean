/- 第13章 場合の数と確率
   13.3 二項定理 -/
import Mathlib

namespace Handbook.C13

-- BOOK: begin binomial
-- 二項定理。係数に Nat.choose が現れる。
example (x y : ℚ) (n : ℕ) :
    (x + y) ^ n =
      ∑ k ∈ Finset.range (n + 1),
        x ^ k * y ^ (n - k) * (Nat.choose n k : ℚ) :=
  add_pow x y n
-- BOOK: end binomial

-- BOOK: begin binomial-sum
-- x = y = 1 とすれば「部分集合の総数 = 2ⁿ」が出る
example (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), Nat.choose n k = 2 ^ n :=
  Nat.sum_range_choose n
-- BOOK: end binomial-sum

end Handbook.C13
