/- 第19章 微分
   19.6 Taylor の定理 / 19.7 l'Hôpital の定理 -/
import Mathlib

namespace Handbook.C19

-- BOOK: begin taylor-lagrange
-- Taylor の定理(Lagrange の剰余項)。
-- 剰余の c は平均値の定理の c と同じ性格で、値は分からない
#check @taylor_mean_remainder_lagrange

-- 多項式部分。n 次までの近似を与える
#check @taylorWithinEval
-- BOOK: end taylor-lagrange

-- BOOK: begin lhopital
-- l'Hôpital の定理。0/0 型の極限を導関数の比に置き換える
#check @HasDerivAt.lhopital_zero_nhds

-- 無限大での形も別に用意されている
#check @deriv.lhopital_zero_atTop
-- BOOK: end lhopital

-- BOOK: begin contdiff
-- C^n 級・C^∞ 級。何回微分できるかを型クラスの引数で表す
#check @ContDiff

-- 高階の導関数
#check @iteratedDeriv
-- BOOK: end contdiff

-- BOOK: begin diff-cont
-- 微分可能なら連続。逆は成り立たない(|x| が反例)
example (f : ℝ → ℝ) (x : ℝ) (h : DifferentiableAt ℝ f x) :
    ContinuousAt f x :=
  h.continuousAt
-- BOOK: end diff-cont

end Handbook.C19
