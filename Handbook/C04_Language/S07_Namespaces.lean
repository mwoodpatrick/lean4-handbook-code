/- 第4章 Lean 言語の基礎
   4.7 名前空間と open -/
import Mathlib

namespace Handbook.C04

-- BOOK: begin ns-basic
namespace Geometry

def area (w h : ℚ) : ℚ := w * h

end Geometry

#eval Geometry.area 3 4  -- 出力: 12

open Geometry in
#eval area 5 6           -- 出力: 30
-- BOOK: end ns-basic

-- BOOK: begin ns-dot
-- 第1引数の型の名前空間は「ドット記法」で呼べる
#eval (6 : ℕ).gcd 4      -- 出力: 2(Nat.gcd 6 4 と同じ)
#eval [3, 1, 2].reverse  -- 出力: [2, 1, 3](List.reverse)
-- BOOK: end ns-dot

-- BOOK: begin ns-open
-- open は名前空間の中身を現在のスコープへ持ち込む
open Real in
#check sqrt 2  -- Real.sqrt 2 : ℝ(open で「sqrt」と呼べる)

section
open List in
#eval range 4  -- 出力: [0, 1, 2, 3]
end
-- BOOK: end ns-open

end Handbook.C04
