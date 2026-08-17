/- 第7章 方程式と不等式
   7.4 相加相乗平均と有名不等式 -/
import Mathlib

namespace Handbook.C07

-- BOOK: begin amgm-two
-- 相加相乗平均(2変数、平方根を避けた形): ab ≤ ((a+b)/2)²
-- 種明かしは (a-b)² ≥ 0。それを nlinarith に手渡す。
example (a b : ℚ) : a * b ≤ ((a + b) / 2) ^ 2 := by
  nlinarith [sq_nonneg (a - b)]
-- BOOK: end amgm-two

-- BOOK: begin positivity
-- 「正である」「非負である」専門のタクティク positivity
example (x : ℚ) (hx : 0 < x) : 0 < x ^ 2 + x := by positivity

example (a b : ℚ) : 0 ≤ a ^ 2 + b ^ 2 := by positivity
-- BOOK: end positivity

-- BOOK: begin amgm-cauchy
-- コーシー–シュワルツ(2次元版)も nlinarith の射程内
example (a b x y : ℚ) :
    (a * x + b * y) ^ 2 ≤ (a ^ 2 + b ^ 2) * (x ^ 2 + y ^ 2) := by
  nlinarith [sq_nonneg (a * y - b * x)]
-- BOOK: end amgm-cauchy

-- BOOK: begin amgm-harmonic
-- 調和平均 ≤ 相加平均: 2ab/(a+b) ≤ (a+b)/2
-- 差を計算すると (a−b)²/(2(a+b)) ≥ 0 になる
example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    2 * a * b / (a + b) ≤ (a + b) / 2 := by
  have hab : 0 < a + b := by linarith
  have h : (a + b) / 2 - 2 * a * b / (a + b)
      = (a - b) ^ 2 / (2 * (a + b)) := by
    field_simp [hab.ne']
    ring
  have h2 : 0 ≤ (a - b) ^ 2 / (2 * (a + b)) := by positivity
  linarith
-- BOOK: end amgm-harmonic

-- BOOK: begin amgm-maxprod
-- 応用: 和が 10 の2数の積は 25 が最大(5 と 5 のとき)
example (x : ℝ) : x * (10 - x) ≤ 25 := by
  nlinarith [sq_nonneg (x - 5)]
-- BOOK: end amgm-maxprod

-- BOOK: begin amgm-three-sq
-- 対称3変数の基本不等式。平方3つを渡せば nlinarith が組み立てる。
example (a b c : ℝ) :
    a * b + b * c + c * a ≤ a ^ 2 + b ^ 2 + c ^ 2 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c),
             sq_nonneg (c - a)]
-- BOOK: end amgm-three-sq

end Handbook.C07
