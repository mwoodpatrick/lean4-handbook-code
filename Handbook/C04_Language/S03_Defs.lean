/- 第4章 Lean 言語の基礎
   4.3 定義とパターンマッチ -/
import Mathlib

namespace Handbook.C04

-- BOOK: begin defs-if
-- コラッツ写像: 偶数なら半分、奇数なら 3n+1
def collatzStep (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

#eval collatzStep 7   -- 出力: 22
#eval collatzStep 22  -- 出力: 11
-- BOOK: end defs-if

-- BOOK: begin defs-rec
-- 再帰的定義。0 から n までの総和。
def sumTo : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumTo n + (n + 1)

#eval sumTo 10  -- 出力: 55
-- BOOK: end defs-rec

-- BOOK: begin defs-match
-- match 式はパターンで場合分けする
def describe (n : ℕ) : String :=
  match n with
  | 0 => "ゼロ"
  | 1 => "いち"
  | _ => "たくさん"

#eval describe 0  -- 出力: "ゼロ"
#eval describe 7  -- 出力: "たくさん"
-- BOOK: end defs-match

-- BOOK: begin defs-where
-- 補助定義は where で本体の後ろに置ける(ヘロンの公式)
def heron2 (a b c : ℚ) : ℚ :=
  s * (s - a) * (s - b) * (s - c)
where
  s : ℚ := (a + b + c) / 2

#eval heron2 3 4 5  -- 出力: 36(面積の2乗。3:4:5 なら面積 6)
-- BOOK: end defs-where

-- BOOK: begin defs-listsum
-- リストの再帰。:: は「先頭 + 残り」への分解。
def total : List ℚ → ℚ
  | [] => 0
  | x :: rest => x + total rest

#eval total [1, 2, 3, 4]  -- 出力: 10
-- BOOK: end defs-listsum

-- BOOK: begin defs-sumto-check
-- 定義した関数についての主張は、そのまま定理になる
example : sumTo 100 = 5050 := by rfl
example (n : ℕ) : sumTo (n + 1) = sumTo n + (n + 1) := rfl
-- BOOK: end defs-sumto-check

end Handbook.C04
