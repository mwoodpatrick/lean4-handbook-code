/- 第35章 数論
   35.6 素数分布 -/
import Mathlib

namespace Handbook.C35

-- BOOK: begin infinitude
-- 素数は無限個ある(ユークリッド、紀元前300年頃)
example (n : ℕ) : ∃ p, n ≤ p ∧ p.Prime :=
  Nat.exists_infinite_primes n
-- BOOK: end infinitude

-- BOOK: begin bertrand
-- ベルトランの仮説: n と 2n の間に必ず素数がある
example (n : ℕ) (hn : n ≠ 0) : ∃ p, p.Prime ∧ n < p ∧ p ≤ 2 * n :=
  Nat.bertrand n hn

-- n = 10 での確認。11, 13, 17, 19 が範囲に入る
example : Nat.Prime 11 ∧ 10 < 11 ∧ 11 ≤ 20 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩
-- BOOK: end bertrand

-- BOOK: begin prime-counting
-- 素数の個数を数える関数。π(10) = 4(2, 3, 5, 7)
example : (Finset.range 11).filter Nat.Prime = {2, 3, 5, 7} := by
  decide

-- 素因数分解の一意性(算術の基本定理、第14章)
example (n : ℕ) (hn : n ≠ 0) :
    n = n.factorization.prod (· ^ ·) :=
  (Nat.prod_factorization_pow_eq_self hn).symm
-- BOOK: end prime-counting

end Handbook.C35
