/- 第35章 数論
   35.4 代数体と整数環 / 35.5 イデアル類群 -/
import Mathlib

namespace Handbook.C35

-- BOOK: begin number-field
-- 代数体: ℚ の有限次拡大。ℚ 自身が最小の例
#check @NumberField

-- その整数環。ℚ に対しては ℤ にあたる
#check @NumberField.RingOfIntegers
-- BOOK: end number-field

-- BOOK: begin algebraic-int
-- 代数的整数: モニックな整数係数多項式の根。√2 はその例
example : IsIntegral ℤ (Real.sqrt 2) := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C 2, ?_, ?_⟩
  · exact Polynomial.monic_X_pow_sub_C 2 (by norm_num)
  · simp

-- 1/2 は代数的だが代数的整数ではない(分母が残る)
example : IsIntegral ℚ ((1 : ℚ) / 2) :=
  isIntegral_algebraMap
-- BOOK: end algebraic-int

-- BOOK: begin class-group
-- イデアル類群: 一意分解がどれだけ壊れているかを測る群
#check @ClassGroup

-- 代数体の整数環では類群が有限(類数の有限性)
#check @ClassGroup.fintypeOfAdmissibleOfFinite
-- BOOK: end class-group

end Handbook.C35
