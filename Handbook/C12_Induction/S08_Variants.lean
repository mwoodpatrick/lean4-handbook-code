/- 第12章 数列と数学的帰納法
   12.8 帰納法のバリアント -/
import Mathlib

namespace Handbook.C12

-- BOOK: begin var-from
-- 途中から始める帰納法。n ≥ 5 でだけ成り立つ主張に使う
example (n : ℕ) (hn : 5 ≤ n) : 2 ^ n > n ^ 2 := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h1 : 1 ≤ n := by omega
    calc 2 ^ (n + 1) = 2 * 2 ^ n := by ring
      _ > 2 * n ^ 2 := by omega
      _ ≥ (n + 1) ^ 2 := by nlinarith
-- BOOK: end var-from

-- BOOK: begin var-list
-- 構造的帰納法。リストの形に沿って進む
example (l : List ℕ) : l.reverse.length = l.length := by
  induction l with
  | nil => rfl
  | cons a t ih => simp
-- BOOK: end var-list

-- BOOK: begin var-two
-- 2段前を使う帰納法。フィボナッチ型の漸化式に対応する
example (n : ℕ) : Nat.fib n ≤ 2 ^ n := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num
  | one => norm_num
  | more n ih1 ih2 =>
    rw [Nat.fib_add_two]
    calc Nat.fib n + Nat.fib (n + 1) ≤ 2 ^ n + 2 ^ (n + 1) := by
          omega
      _ ≤ 2 ^ (n + 2) := by ring_nf; omega
-- BOOK: end var-two

end Handbook.C12
