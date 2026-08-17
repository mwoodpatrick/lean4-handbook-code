/- 第11章 指数関数と対数関数
   11.2 実数乗と rpow — 3つのべき乗の使い分け -/
import Mathlib

namespace Handbook.C11

-- BOOK: begin rpow-three
-- 同じ ^ でも指数の型で別の演算になる
#check (2 : ℝ) ^ (3 : ℕ)    -- 自然数乗(npow)
#check (2 : ℝ) ^ (-3 : ℤ)   -- 整数乗(zpow)
#check (2 : ℝ) ^ (0.5 : ℝ)  -- 実数乗(Real.rpow)
-- BOOK: end rpow-three

-- BOOK: begin rpow-sqrt
-- 平方根は 1/2 乗である
example (x : ℝ) : Real.sqrt x = x ^ (1 / 2 : ℝ) :=
  Real.sqrt_eq_rpow x
-- BOOK: end rpow-sqrt

-- BOOK: begin rpow-twelfth
-- 半音 2^(1/12) を12回重ねるとちょうど2倍(オクターブ)
example : ((2 : ℝ) ^ ((1 : ℝ) / 12)) ^ (12 : ℕ) = 2 := by
  rw [← Real.rpow_natCast ((2 : ℝ) ^ ((1 : ℝ) / 12)) 12,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    show (1 : ℝ) / 12 * ((12 : ℕ) : ℝ) = 1 by
      push_cast; norm_num,
    Real.rpow_one]
-- BOOK: end rpow-twelfth

end Handbook.C11
