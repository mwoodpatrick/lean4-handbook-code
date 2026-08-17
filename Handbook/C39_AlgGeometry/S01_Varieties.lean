/- 第39章 代数幾何入門
   39.1 代数曲線 / 39.2 アフィン多様体 -/
import Mathlib

namespace Handbook.C39

-- BOOK: begin curves
-- 代数曲線: 多項式の零点集合。円は x² + y² - 1 = 0
example (x y : ℝ) : x ^ 2 + y ^ 2 - 1 = 0 ↔ x ^ 2 + y ^ 2 = 1 := by
  constructor <;> intro h <;> linarith

-- 楕円曲線 y² = x³ - x 上の点(0, 0)
example : (0 : ℝ) ^ 2 = 0 ^ 3 - 0 := by norm_num

-- 点(1, 0)も乗っている
example : (0 : ℝ) ^ 2 = 1 ^ 3 - 1 := by norm_num
-- BOOK: end curves

-- BOOK: begin mvpolynomial
-- 多変数多項式環。変数の個数を型で持つ
#check @MvPolynomial

-- 2変数多項式 X₀ + X₁ を (3, 4) で評価すると 7
example :
    MvPolynomial.eval (fun i : Fin 2 => if i = 0 then (3 : ℤ) else 4)
      (MvPolynomial.X 0 + MvPolynomial.X 1) = 7 := by
  simp
-- BOOK: end mvpolynomial

end Handbook.C39
