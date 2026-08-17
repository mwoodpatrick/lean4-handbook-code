/- 第41章 証明自動化
   41.5 代数系 tactic の適用範囲 -/
import Mathlib

namespace Handbook.C41

-- BOOK: begin ring
-- ring: 可換環の等式。変数を含んでよいが等式限定
example (x : ℚ) : x ^ 2 - 1 = (x - 1) * (x + 1) := by ring
example (R : Type) [CommRing R] (a b : R) :
    (a + b) ^ 3 = a ^ 3 + 3 * a ^ 2 * b + 3 * a * b ^ 2 + b ^ 3 := by
  ring
-- BOOK: end ring

-- BOOK: begin linarith
-- linarith: 線形不等式。仮定の線形結合で矛盾を作る
example (x y : ℝ) (h1 : x ≤ 3) (h2 : y ≤ 2) : x + y ≤ 5 := by
  linarith

-- nlinarith は非線形項も少し扱える。補助項をヒントで渡す
example (x : ℝ) : 0 ≤ x ^ 2 + 2 * x + 1 := by
  nlinarith [sq_nonneg (x + 1)]
-- BOOK: end linarith

-- BOOK: begin positivity
-- positivity: 「明らかに正/非負」を構文から判定する
example (x : ℝ) (hx : 0 < x) : 0 < x ^ 2 + Real.exp x := by
  positivity

example (x : ℝ) : 0 ≤ |x| + x ^ 2 := by positivity
-- BOOK: end positivity

-- BOOK: begin gcongr
-- gcongr: 単調性による部分項の入れ替え
example (a b c : ℝ) (h : a ≤ b) (hc : 0 ≤ c) :
    a * c ≤ b * c := by
  gcongr

example (a b : ℝ) (h : a ≤ b) : a + 5 ≤ b + 5 := by gcongr
-- BOOK: end gcongr

end Handbook.C41
