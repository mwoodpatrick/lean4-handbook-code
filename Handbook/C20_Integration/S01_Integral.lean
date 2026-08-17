/- 第20章 積分
   20.1 積分の定義 / 20.2 intervalIntegral と計算規則 -/
import Mathlib

namespace Handbook.C20

open intervalIntegral

-- BOOK: begin int-basic
-- 区間積分 ∫ x in a..b, f x。多項式の積分は公式で計算できる。
example : ∫ x in (0:ℝ)..1, x = 1 / 2 := by
  rw [integral_id]
  norm_num

example : ∫ x in (0:ℝ)..1, x ^ 2 = 1 / 3 := by
  rw [integral_pow]
  norm_num
-- BOOK: end int-basic

-- BOOK: begin int-sin
-- ∫₀^π sin x dx = 2。教科書の名物計算。
example : ∫ x in (0:ℝ)..Real.pi, Real.sin x = 2 := by
  rw [integral_sin]
  norm_num [Real.cos_pi, Real.cos_zero]
-- BOOK: end int-sin

-- BOOK: begin int-const
-- 定数の積分は「高さ × 幅」の長方形の面積
example (c : ℝ) (a b : ℝ) : ∫ _ in a..b, c = (b - a) * c := by
  rw [integral_const]; ring
-- BOOK: end int-const

-- BOOK: begin int-symm
-- 向き付き積分: 端を入れ替えると符号が反転する
example (f : ℝ → ℝ) (a b : ℝ) :
    ∫ x in b..a, f x = -∫ x in a..b, f x :=
  integral_symm a b

-- 区間の連結: [a,b] と [b,c] の積分を足すと [a,c] の積分
example (f : ℝ → ℝ) (a b c : ℝ)
    (hab : IntervalIntegrable f MeasureTheory.volume a b)
    (hbc : IntervalIntegrable f MeasureTheory.volume b c) :
    (∫ x in a..b, f x) + ∫ x in b..c, f x = ∫ x in a..c, f x :=
  integral_add_adjacent_intervals hab hbc
-- BOOK: end int-symm

end Handbook.C20
