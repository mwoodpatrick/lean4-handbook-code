/- 第5章 証明の基本
   5.7 simp — 正しい使い方と落とし穴 -/
import Mathlib

namespace Handbook.C05

-- BOOK: begin simp-basic
-- simp は「簡約向きの等式」を繰り返し適用する
example (a : ℕ) : (a + 0) * 1 = a := by simp

example (xs : List ℕ) : (xs ++ []).length = xs.length := by
  simp
-- BOOK: end simp-basic

-- BOOK: begin simp-only
-- simp only は使う補題を明示する(暴走しない simp)
example (a b : ℕ) : a + 0 + (b + 0) = a + b := by
  simp only [Nat.add_zero]
-- BOOK: end simp-only

-- BOOK: begin simp-at
-- 仮定側を簡約するには at を付ける
example (a b : ℕ) (h : a + 0 = b) : a = b := by
  simp at h
  exact h
-- BOOK: end simp-at

-- BOOK: begin simp-with
-- 仮定を簡約規則として渡す(simp only [h])
example (a b : ℕ) (h : b = 2 * a) : a + b = 3 * a := by
  simp only [h]
  ring
-- BOOK: end simp-with

end Handbook.C05
