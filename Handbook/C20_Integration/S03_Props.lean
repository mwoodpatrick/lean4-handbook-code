/- 第20章 積分
   20.3 積分の性質 -/
import Mathlib

namespace Handbook.C20

open intervalIntegral

-- BOOK: begin int-linear
-- 線形性: 和の積分は積分の和
#check @intervalIntegral.integral_add

-- 定数倍も外に出せる
#check @intervalIntegral.integral_smul
-- BOOK: end int-linear

-- BOOK: begin int-additive
-- 区間の加法性: [a,b] と [b,c] をつなぐと [a,c] になる
#check @intervalIntegral.integral_add_adjacent_intervals
-- BOOK: end int-additive

-- BOOK: begin int-mono
-- 単調性: f ≤ g なら積分も ≤。評価の出発点になる
example (f g : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hf : IntervalIntegrable f MeasureTheory.volume a b)
    (hg : IntervalIntegrable g MeasureTheory.volume a b)
    (h : ∀ x ∈ Set.Icc a b, f x ≤ g x) :
    ∫ x in a..b, f x ≤ ∫ x in a..b, g x :=
  intervalIntegral.integral_mono_on hab hf hg h
-- BOOK: end int-mono

-- BOOK: begin int-abs
-- 三角不等式の積分版。|∫f| ≤ ∫|f|
#check @intervalIntegral.abs_integral_le_integral_abs
-- BOOK: end int-abs

end Handbook.C20
