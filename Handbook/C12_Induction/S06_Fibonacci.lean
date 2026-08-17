/- 第12章 数列と数学的帰納法
   12.6 漸化式とフィボナッチ数列 -/
import Mathlib

namespace Handbook.C12

-- BOOK: begin fib-def
-- 2 項前までを参照する漸化式。定義がそのまま Lean のコードになる。
def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

#eval (List.range 8).map fib  -- 出力: [0, 1, 1, 2, 3, 5, 8, 13]
-- BOOK: end fib-def

-- 漸化式そのものは定義から rfl で取り出せる
theorem fib_add_two (n : ℕ) :
    fib (n + 2) = fib n + fib (n + 1) := rfl

-- BOOK: begin fib-sum
-- 最初の n 項の和は fib (n+1) - 1。引き算を避けて +1 の形で述べる。
theorem fib_sum (n : ℕ) :
    (∑ i ∈ Finset.range n, fib i) + 1 = fib (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Finset.sum_range_succ, add_right_comm, ih]
    have h : fib (n + 1 + 1) = fib n + fib (n + 1) := rfl
    omega
-- BOOK: end fib-sum

-- BOOK: begin fib-mathlib
-- mathlib の Nat.fib と一致する(functional induction による証明)
theorem fib_eq_nat_fib (n : ℕ) : fib n = Nat.fib n := by
  induction n using fib.induct with
  | case1 => rfl
  | case2 => rfl
  | case3 n ih1 ih2 =>
    rw [fib_add_two, Nat.fib_add_two, ih1, ih2]
-- BOOK: end fib-mathlib

-- BOOK: begin fib-even
-- fib (3n) は偶数である。3 つ先の漸化式を用意して普通の帰納法で示す。
theorem fib_add_three (n : ℕ) :
    fib (n + 3) = 2 * fib (n + 1) + fib n := by
  have h : fib (n + 3) = fib (n + 1) + (fib n + fib (n + 1)) := rfl
  omega

theorem two_dvd_fib_three_mul (n : ℕ) : 2 ∣ fib (3 * n) := by
  induction n with
  | zero => simp [fib]
  | succ n ih =>
    have h3 : 3 * (n + 1) = 3 * n + 3 := by ring
    rw [h3, fib_add_three]
    omega
-- BOOK: end fib-even

end Handbook.C12
