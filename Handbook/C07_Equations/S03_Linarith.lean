/- 第7章 方程式と不等式
   7.3 不等式の基本 -/
import Mathlib

namespace Handbook.C07

-- BOOK: begin lin-basic
-- linarith は線形な不等式の組み合わせを自動で閉じる
example (x : ℚ) (h : 2 * x + 3 < 11) : x < 4 := by linarith

example (x y : ℚ) (h1 : x + 2 * y ≤ 4) (h2 : 1 ≤ y) :
    x ≤ 2 := by linarith
-- BOOK: end lin-basic

-- BOOK: begin lin-chain
-- 推移律の連鎖も一撃
example (a b c d : ℚ) (h1 : a < b) (h2 : b ≤ c) (h3 : c < d) :
    a < d := by linarith
-- BOOK: end lin-chain

-- BOOK: begin lin-mul
-- 積が入ると linarith の外。不等式×正数は専用の補題で。
example (a b c : ℚ) (h : a < b) (hc : 0 < c) :
    a * c < b * c :=
  mul_lt_mul_of_pos_right h hc

-- 両辺に足す・引くは linarith の内側
example (a b : ℚ) (h : a < b) : a + 5 < b + 5 := by linarith
-- BOOK: end lin-mul

end Handbook.C07
