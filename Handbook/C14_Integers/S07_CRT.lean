/- 第14章 整数の世界
   14.4b 中国剰余定理 -/
import Mathlib

namespace Handbook.C14

-- BOOK: begin crt-example
-- 3 で割って 2 余り、5 で割って 3 余る数は、15 を法で 8 に定まる
example : (8 : ℕ) % 3 = 2 ∧ (8 : ℕ) % 5 = 3 := by decide

-- 15 未満でその条件を満たすのは 8 だけである
example : ∀ n < 15, n % 3 = 2 ∧ n % 5 = 3 → n = 8 := by decide
-- BOOK: end crt-example

-- BOOK: begin crt-equiv
-- 一般形: 互いに素な法に分解すると環として同型になる
#check @ZMod.chineseRemainder

-- ℤ/(3·5) ≃ ℤ/3 × ℤ/5。左辺は積の形で書く必要がある
noncomputable example :
    ZMod (3 * 5) ≃+* ZMod 3 × ZMod 5 :=
  ZMod.chineseRemainder (by norm_num)
-- BOOK: end crt-equiv

-- BOOK: begin crt-coprime
-- 互いに素でないと壊れる。ℤ/4 と ℤ/2 × ℤ/2 は同型でない
-- (左は位数 4 の元を持つが、右は持たない)
example : ((2 : ZMod 4) + 2) = 0 := by decide

example : ∀ x : ZMod 2 × ZMod 2, x + x = 0 := by decide
-- BOOK: end crt-coprime

end Handbook.C14
