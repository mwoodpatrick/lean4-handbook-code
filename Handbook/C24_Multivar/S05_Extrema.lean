/- 第24章 多変数の微積分
   24.6 極値問題とヘッセ行列 -/
import Mathlib

namespace Handbook.C24

-- BOOK: begin extrema-min
-- 原点は f(x,y) = x² + y² の局所最小点
example : IsLocalMin (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) 0 :=
  Filter.Eventually.of_forall fun p => by simp; positivity
-- BOOK: end extrema-min

-- BOOK: begin extrema-fermat
-- 内点の極値では全微分が消える(多変数版フェルマーの定理)
#check @IsLocalMin.fderiv_eq_zero
#check @IsLocalMax.fderiv_eq_zero

-- 仮定つきの形。全微分の存在を与えると 0 だと言える
example (f : ℝ × ℝ → ℝ) (f' : ℝ × ℝ →L[ℝ] ℝ) (x : ℝ × ℝ)
    (hmax : IsLocalMax f x) (hf : HasFDerivAt f f' x) : f' = 0 :=
  hmax.hasFDerivAt_eq_zero hf
-- BOOK: end extrema-fermat

-- BOOK: begin extrema-hessian
-- 2 階の全微分。ヘッセ行列はこの二重線形写像の行列表示
#check @iteratedFDeriv

-- 対称性: 混合偏微分の順序は交換できる(シュワルツの定理)
#check @second_derivative_symmetric
-- BOOK: end extrema-hessian

-- BOOK: begin extrema-convex
-- 凸関数では局所最小が大域最小になる
#check @ConvexOn

-- 全域で凸なら、局所最小はすべての点より小さい
example (f : ℝ × ℝ → ℝ) (a : ℝ × ℝ) (hmin : IsLocalMin f a)
    (hconv : ConvexOn ℝ Set.univ f) : ∀ x, f a ≤ f x :=
  IsMinOn.of_isLocalMin_of_convex_univ hmin hconv
-- BOOK: end extrema-convex

-- BOOK: begin extrema-lagrange
-- 制約つき極値: ラグランジュの未定乗数法。
-- 制約面上の極値点では、2つの勾配が平行になる
#check @IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt_1d
-- BOOK: end extrema-lagrange

end Handbook.C24
