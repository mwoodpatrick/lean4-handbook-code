/- 第12章 数列と数学的帰納法
   12.9 帰納法が詰まったら仮定を強める -/
import Mathlib

namespace Handbook.C12

-- BOOK: begin str-target
-- 目標: 奇数の総和が平方数になる。1+3+5+…+(2n-1) = n²
example (n : ℕ) :
    ∑ i ∈ Finset.range n, (2 * i + 1) = n ^ 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring
-- BOOK: end str-target

-- BOOK: begin str-weak
-- 強めた形。「両者が等しい」ほうが帰納法を回しやすい。
-- 一方だけを ≤ で示そうとすると仮定が足りなくなる。
example (n : ℕ) :
    ∑ i ∈ Finset.range n, (2 * i + 1) ≤ n ^ 2 := by
  -- 等式を経由する。不等式のままでは ih が弱すぎて回らない
  have h : ∑ i ∈ Finset.range n, (2 * i + 1) = n ^ 2 := by
    induction n with
    | zero => rfl
    | succ n ih => rw [Finset.sum_range_succ, ih]; ring
  omega
-- BOOK: end str-weak

-- BOOK: begin str-general
-- 一般化して強める典型例。
-- 「a n = 2^n - 1」を示すには漸化式の形をそのまま追う
def a : ℕ → ℕ
  | 0 => 0
  | n + 1 => 2 * a n + 1

example (n : ℕ) : a n = 2 ^ n - 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    simp only [a, ih]
    omega
-- BOOK: end str-general

end Handbook.C12
