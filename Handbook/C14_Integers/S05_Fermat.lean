/- 第14章 整数の世界
   14.5 フェルマーの小定理 / 14.7 決定手続き -/
import Mathlib

namespace Handbook.C14

instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

-- BOOK: begin fermat-eval
-- まず数値で観察する: 2⁶ = 64 = 7 × 9 + 1
#eval (2 ^ 6 : ZMod 7)  -- 出力: 1
#eval (3 ^ 6 : ZMod 7)  -- 出力: 1
#eval (5 ^ 6 : ZMod 7)  -- 出力: 1
-- BOOK: end fermat-eval

-- BOOK: begin fermat-little
-- フェルマーの小定理: p が素数、a ≢ 0 なら a^(p-1) ≡ 1
example (a : ZMod 7) (ha : a ≠ 0) : a ^ 6 = 1 :=
  ZMod.pow_card_sub_one_eq_one ha
-- BOOK: end fermat-little

-- BOOK: begin omega-demo
-- omega: 整数・自然数の線形算術の決定手続き
example (a b : ℤ) (h : 2 * a + 6 * b = 5) : False := by omega

example (n : ℕ) : (n + 7) % 7 = n % 7 := by omega
-- BOOK: end omega-demo

-- BOOK: begin totient
-- オイラー関数 φ(n): n 未満で n と互いに素な数の個数
#eval Nat.totient 12  -- 出力: 4(1, 5, 7, 11)
#eval Nat.totient 7   -- 出力: 6(素数 p では p−1)

example : Nat.totient 12 = 4 := by decide
-- BOOK: end totient

-- BOOK: begin integers-exercises
-- 演習: 互除法・合同式・整除
example : Nat.gcd 84 60 = 12 := by decide

example : (10 : ZMod 7) = 3 := by decide

example (a : ℤ) (h : 4 ∣ a) : 2 ∣ a := by omega
-- BOOK: end integers-exercises

end Handbook.C14
