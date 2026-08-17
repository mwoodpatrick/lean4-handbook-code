/- 第12章 数列と数学的帰納法
   12.3 総和と Finset.sum -/
import Mathlib

namespace Handbook.C12

-- BOOK: begin sum-eval
-- Σ は Finset.sum。range n = {0, 1, …, n-1} 上の和として書く。
open Finset in
#eval ∑ i ∈ range 5, i ^ 2  -- 出力: 30
-- BOOK: end sum-eval

-- BOOK: begin gauss
-- ガウスの和 1 + 2 + ⋯ + n = n(n+1)/2。割り算を避けて 2 倍で述べる。
theorem gauss_sum (n : ℕ) :
    2 * ∑ i ∈ Finset.range (n + 1), i = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.mul_add, ih]
    ring
-- BOOK: end gauss

-- BOOK: begin gauss-mathlib
-- mathlib には既に同じ内容の補題がある
example (n : ℕ) :
    (∑ i ∈ Finset.range n, i) * 2 = n * (n - 1) :=
  Finset.sum_range_id_mul_two n
-- BOOK: end gauss-mathlib

-- BOOK: begin geom-sum
-- 等比数列の和。体 ℚ では商の形で書ける(r ≠ 1)。
example (r : ℚ) (hr : r ≠ 1) (n : ℕ) :
    ∑ i ∈ Finset.range n, r ^ i = (r ^ n - 1) / (r - 1) :=
  geom_sum_eq hr n
-- BOOK: end geom-sum

-- BOOK: begin telescope
-- 望遠鏡和: 隣接差の和は両端だけが残る
example (f : ℕ → ℤ) (n : ℕ) :
    ∑ i ∈ Finset.range n, (f (i + 1) - f i) = f n - f 0 :=
  Finset.sum_range_sub f n
-- BOOK: end telescope

-- BOOK: begin sum-squares
-- 平方和の公式。割り算を避けて 6 倍の形で述べる。
theorem sum_sq (n : ℕ) :
    6 * ∑ i ∈ Finset.range (n + 1), i ^ 2
      = n * (n + 1) * (2 * n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.mul_add, ih]
    ring
-- BOOK: end sum-squares

end Handbook.C12
