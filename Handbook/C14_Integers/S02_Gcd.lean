/- 第14章 整数の世界
   14.2 最大公約数とユークリッドの互除法 -/
import Mathlib

namespace Handbook.C14

-- BOOK: begin gcd-basic
#eval Nat.gcd 12 18  -- 出力: 6

-- 互除法の1歩がそのまま定理になっている
example (a b : ℕ) : Nat.gcd a b = Nat.gcd (b % a) a :=
  Nat.gcd_rec a b

example (a b : ℕ) : Nat.gcd a b ∣ a := Nat.gcd_dvd_left a b
-- BOOK: end gcd-basic

-- BOOK: begin gcd-bezout
-- ベズーの補題: gcd は a, b の整数係数の線形結合で書ける
example (a b : ℤ) :
    ∃ x y : ℤ, (Int.gcd a b : ℤ) = a * x + b * y :=
  ⟨Int.gcdA a b, Int.gcdB a b, Int.gcd_eq_gcd_ab a b⟩
-- BOOK: end gcd-bezout

-- BOOK: begin gcd-bezout-compute
-- ベズー係数は互除法の逆走で計算できる(拡張ユークリッド)
#eval Int.gcdA 3 5  -- 出力: 2
#eval Int.gcdB 3 5  -- 出力: -1

-- 検算: 3·2 + 5·(−1) = 1 = gcd(3, 5)
example : (3 : ℤ) * 2 + 5 * (-1) = 1 := by norm_num
-- BOOK: end gcd-bezout-compute

-- BOOK: begin gcd-trace
-- 互除法の実行トレース: gcd(252, 105) を手で追う
#eval Nat.gcd 252 105  -- 出力: 21
-- 252 = 105·2 + 42 → 105 = 42·2 + 21 → 42 = 21·2 + 0
example : Nat.gcd 252 105 = 21 := by decide

-- 最小公倍数は「積 = gcd × lcm」で結ばれる
example (a b : ℕ) : Nat.gcd a b * Nat.lcm a b = a * b :=
  Nat.gcd_mul_lcm a b
-- BOOK: end gcd-trace

-- BOOK: begin gcd-coprime
-- 互いに素 = gcd が 1。既約分数の言い換えでもある。
example : Nat.Coprime 8 15 := by decide

-- 互いに素なら「積を割るなら片方を割る」(ユークリッドの補題)
example (k m n : ℕ) (hk : Nat.Coprime k m) (h : k ∣ m * n) :
    k ∣ n :=
  hk.dvd_of_dvd_mul_left h
-- BOOK: end gcd-coprime

end Handbook.C14
