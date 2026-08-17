/- 第6章 数と式
   6.5 数値を確かめる -/
import Mathlib

namespace Handbook.C06

-- BOOK: begin nn-intro
-- 本章冒頭の主張。電卓の結果ではなく、検査済みの定理である。
example : 999 * 1001 = 999999 := by norm_num

example : (1 : ℚ) / 7 < 1 / 6 := by norm_num
example : 2 ^ 10 = 1024 := by norm_num
-- BOOK: end nn-intro

-- BOOK: begin nn-basic
example : (123 : ℕ) * 321 = 39483 := by norm_num

example : (2 : ℚ) / 3 + 1 / 6 = 5 / 6 := by norm_num

-- norm_num は素数判定の拡張を持つ
example : Nat.Prime 2027 := by norm_num
-- BOOK: end nn-basic

-- BOOK: begin nn-decide
-- 小さな整除の主張なら decide の全数検査でもよい
example : 3 ∣ 111 := by decide
example : ¬ 7 ∣ 100 := by decide
-- BOOK: end nn-decide

-- BOOK: begin numbers-exercises
-- 演習: 本章の道具(ring・norm_num・絶対値の補題)で3問
example (x : ℚ) : (x + 5) ^ 2 - (x - 5) ^ 2 = 20 * x := by
  ring

example : Nat.Prime 101 := by norm_num

example (a : ℚ) (h : |a| < 2) : -2 < a := (abs_lt.mp h).1
-- BOOK: end numbers-exercises

end Handbook.C06
