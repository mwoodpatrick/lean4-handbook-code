/- 第4章 Lean 言語の基礎
   4.1 式と評価 -/
import Mathlib

namespace Handbook.C04

-- BOOK: begin eval-basic
#eval 2 + 3 * 4    -- 出力: 14
#eval (2 + 3) * 4  -- 出力: 20
#eval 7 / 2        -- 出力: 3(自然数の割り算は切り捨て)
#eval 7 % 2        -- 出力: 1
-- BOOK: end eval-basic

-- BOOK: begin eval-check
-- #eval が「値」を返すのに対し、#check は「型」を返す
#check 2 + 3               -- 2 + 3 : ℕ
#check (2 + 3 : ℤ)         -- 2 + 3 : ℤ
#check fun x : ℕ => x + 1  -- fun x => x + 1 : ℕ → ℕ
-- BOOK: end eval-check

-- BOOK: begin eval-divzero
-- 0 で割ってもエラーにならない(規約: x / 0 = 0)
#eval 7 / 0        -- 出力: 0
#eval (7 : ℚ) / 0  -- 出力: 0
-- BOOK: end eval-divzero

-- BOOK: begin eval-let
-- let は値に局所的な名前を付ける
#eval let s := 1 + 2 + 3 + 4; s * s      -- 出力: 100
#eval let x := 10; let y := x + 5; x * y -- 出力: 150
-- BOOK: end eval-let

end Handbook.C04
