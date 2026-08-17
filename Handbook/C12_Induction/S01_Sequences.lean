/- 第12章 数列と数学的帰納法
   12.1 数列は関数である -/
import Mathlib

namespace Handbook.C12

-- BOOK: begin seq-def
-- 数列とは ℕ からの関数にすぎない。奇数列 1, 3, 5, … を定義する。
def oddSeq (n : ℕ) : ℚ := 2 * n + 1

#eval oddSeq 0  -- 出力: 1
#eval oddSeq 3  -- 出力: 7
-- BOOK: end seq-def

-- BOOK: begin seq-mono
-- oddSeq は狭義単調増加である。
-- 隣接項の比較だけで済むのは strictMono_nat_of_lt_succ のおかげ。
theorem oddSeq_strictMono : StrictMono oddSeq := by
  apply strictMono_nat_of_lt_succ
  intro n
  unfold oddSeq
  push_cast
  linarith
-- BOOK: end seq-mono

-- BOOK: begin seq-anon
-- 名前を付けずに数列を書くこともできる(匿名関数)
#eval (fun n : ℕ => n * n) 5  -- 出力: 25
-- BOOK: end seq-anon

-- BOOK: begin seq-bounded
-- 下に有界: すべての項が 1 以上
example (n : ℕ) : 1 ≤ oddSeq n := by
  unfold oddSeq
  have h : (0 : ℚ) ≤ n := Nat.cast_nonneg n
  linarith
-- BOOK: end seq-bounded

end Handbook.C12
