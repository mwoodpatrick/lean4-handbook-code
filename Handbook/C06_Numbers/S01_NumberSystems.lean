/- 第6章 数と式
   6.1 数の体系と型強制 -/
import Mathlib

namespace Handbook.C06

-- BOOK: begin num-coe
-- 自然数 3 を整数として使うとき、型強制 ↑ が挿入される
#check ((3 : ℕ) : ℤ)  -- ↑3 : ℤ

-- 強制をまたぐ計算は push_cast で内側へ整理してから ring
example (n : ℕ) : ((n + 1 : ℕ) : ℚ) = n + 1 := by
  push_cast
  ring
-- BOOK: end num-coe

-- BOOK: begin num-castdown
-- 逆向き(ℚ の等式から ℕ の等式へ)は exact_mod_cast
example (a b : ℕ) (h : (a : ℚ) = b) : a = b := by
  exact_mod_cast h
-- BOOK: end num-castdown

-- BOOK: begin num-why-z
-- ℕ で切り捨てられる引き算も、ℤ に上がれば自由になる
example (n : ℕ) : (n : ℤ) - (n + 1 : ℕ) = -1 := by
  push_cast
  ring

-- ℤ の -3 は ℕ に写せない(図の「左向きの橋はない」の実演)
example : ¬ ∃ n : ℕ, (n : ℤ) = -3 := by
  rintro ⟨n, hn⟩
  omega
-- BOOK: end num-why-z

-- BOOK: begin num-digits
-- 位取り記数法: 45 を2進法で書くと 101101
#eval Nat.digits 2 45   -- 出力: [1, 0, 1, 1, 0, 1](下位桁から)
#eval Nat.digits 10 45  -- 出力: [5, 4]

-- 桁の列から数が復元できることも定理(検算は decide)
example : Nat.ofDigits 2 [1, 0, 1, 1, 0, 1] = 45 := by decide
-- BOOK: end num-digits

-- BOOK: begin num-decimal
-- 有理数の小数展開は必ず循環する。1/7 の循環節は 142857。
#eval (10 ^ 6 / 7 : ℕ)  -- 出力: 142857
#eval 142857 * 7        -- 出力: 999999(= 10⁶ − 1)

-- 「999999 が 7 で割り切れる」ことが循環の正体である
example : 7 ∣ 10 ^ 6 - 1 := by decide
-- BOOK: end num-decimal

end Handbook.C06
