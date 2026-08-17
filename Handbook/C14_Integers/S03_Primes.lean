/- 第14章 整数の世界
   14.3 素数と素因数分解の一意性 -/
import Mathlib

namespace Handbook.C14

-- BOOK: begin prime-basic
example : Nat.Prime 13 := by norm_num

-- 1 でない自然数は素因数を持つ
example (n : ℕ) (h : 2 ≤ n) : ∃ p, p.Prime ∧ p ∣ n :=
  Nat.exists_prime_and_dvd (by omega)
-- BOOK: end prime-basic

-- BOOK: begin prime-factors
-- 素因数分解はリストとして計算できる
#eval Nat.primeFactorsList 360  -- 出力: [2, 2, 2, 3, 3, 5]

-- 分解の積は元に戻る(0 でなければ)
example (n : ℕ) (hn : n ≠ 0) :
    (Nat.primeFactorsList n).prod = n :=
  Nat.prod_primeFactorsList hn
-- BOOK: end prime-factors

-- BOOK: begin prime-euclid-lemma
-- 素数の本質(ユークリッドの補題): 積を割るなら片方を割る
example (p a b : ℕ) (hp : p.Prime) (h : p ∣ a * b) :
    p ∣ a ∨ p ∣ b :=
  hp.dvd_mul.mp h

-- 合成数 6 では成り立たない: 6 ∣ 4·9 だが 6 ∤ 4 かつ 6 ∤ 9
example : (6 ∣ 4 * 9) ∧ ¬(6 ∣ 4) ∧ ¬(6 ∣ 9) := by decide
-- BOOK: end prime-euclid-lemma

-- BOOK: begin divisors
-- 約数の集合・個数・総和はすべて計算できる
#eval (12 : ℕ).divisors         -- 出力: {1, 2, 3, 4, 6, 12}
#eval (12 : ℕ).divisors.card    -- 出力: 6
#eval (12 : ℕ).divisors.sum id  -- 出力: 28

-- 6 は完全数: 自分以外の約数の和(1+2+3)が自分に等しい
example : (6 : ℕ).divisors.sum id = 2 * 6 := by decide
-- BOOK: end divisors

end Handbook.C14
