/- 第6章 数と式
   6.4 絶対値と大小評価 -/
import Mathlib

namespace Handbook.C06

-- BOOK: begin abs-basic
#eval |(-5 : ℤ)|  -- 出力: 5

example (x : ℚ) : 0 ≤ |x| := abs_nonneg x

-- 三角不等式。解析学のすべてがここから始まる。
example (x y : ℚ) : |x + y| ≤ |x| + |y| := abs_add_le x y
-- BOOK: end abs-basic

-- BOOK: begin abs-cases
-- 定義どおりの場合分け: 非負ならそのまま、負なら符号を返す
example (x : ℚ) (h : 0 ≤ x) : |x| = x := abs_of_nonneg h

example (x : ℚ) (h : x < 0) : |x| = -x := abs_of_neg h
-- BOOK: end abs-cases

-- BOOK: begin abs-lt
-- |x| < c は -c < x < c と同じこと
example (x : ℚ) (h : |x| < 1) : -1 < x ∧ x < 1 := abs_lt.mp h

example (x : ℚ) (h1 : -2 < x) (h2 : x < 2) : |x| < 2 :=
  abs_lt.mpr ⟨h1, h2⟩
-- BOOK: end abs-lt

-- BOOK: begin abs-sqrt
-- √(a²) = |a|。「2乗してルート」は元に戻らず、符号を消す。
example (a : ℝ) : Real.sqrt (a ^ 2) = |a| :=
  Real.sqrt_sq_eq_abs a
-- BOOK: end abs-sqrt

-- BOOK: begin abs-eq
-- 絶対値の方程式を「解く」: |x − 3| = 5 ⟺ x = 8 ∨ x = −2
example (x : ℚ) : |x - 3| = 5 ↔ x = 8 ∨ x = -2 := by
  rw [abs_eq (by norm_num : (0 : ℚ) ≤ 5)]
  constructor
  · rintro (h | h)
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl) <;> norm_num
-- BOOK: end abs-eq

-- BOOK: begin abs-rev-triangle
-- 例題: 逆三角不等式。三角不等式1本から導く。
example (a b : ℚ) : |a| - |b| ≤ |a - b| := by
  have h := abs_add_le (a - b) b
  have e : a - b + b = a := by ring
  rw [e] at h
  linarith

-- mathlib には一般形が用意されている
example (a b : ℚ) : |a| - |b| ≤ |a - b| :=
  abs_sub_abs_le_abs_sub a b
-- BOOK: end abs-rev-triangle

end Handbook.C06
