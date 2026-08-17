/- 第36章 多様体
   36.5 接空間と接束 -/
import Mathlib

namespace Handbook.C36

open Manifold

-- BOOK: begin tangent-space
-- 接空間: 各点に貼り付いたベクトル空間
#check @TangentSpace

-- 接束: すべての接空間を束ねた多様体
#check @TangentBundle
-- BOOK: end tangent-space

-- BOOK: begin mfderiv
-- 多様体上の微分。第19章の fderiv の多様体版
#check @mfderiv

-- ℝ 上では通常の微分と一致する
example (f : ℝ → ℝ) (x : ℝ) :
    mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ)
      f x = fderiv ℝ f x := by
  rw [mfderiv_eq_fderiv]
-- BOOK: end mfderiv

end Handbook.C36
