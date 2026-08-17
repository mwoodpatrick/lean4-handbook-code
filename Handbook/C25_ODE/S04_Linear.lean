/- 第25章 微分方程式
   25.7 線形系と行列指数関数 -/
import Mathlib

namespace Handbook.C25

-- BOOK: begin linear-scalar
-- スカラーの場合: (e^{at})' = a·e^{at}。
-- 変化率が現在値に比例する、が指数関数の定義的性質である
example (a t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (a * s))
      (a * Real.exp (a * t)) t := by
  have h := (Real.hasDerivAt_exp (a * t)).comp t
    ((hasDerivAt_id t).const_mul a)
  simpa [Function.comp_def, mul_comm] using h
-- BOOK: end linear-scalar

-- BOOK: begin linear-exp
-- 行列指数関数は Banach 代数の exp の特殊化にすぎない
#check @NormedSpace.exp

-- 冪級数としての定義。第21章の級数がここで効く
#check @NormedSpace.exp_eq_tsum
-- BOOK: end linear-exp

-- BOOK: begin linear-deriv
-- (e^{tA})' = A·e^{tA}。線形系 ẋ = Ax の解が e^{tA}x₀ である根拠
#check @hasDerivAt_exp_smul_const
-- BOOK: end linear-deriv

-- BOOK: begin linear-commute
-- e^{A+B} = e^A·e^B は A と B が可換なときに限る。
-- 行列が非可換だから、この仮定を落とせない
#check @NormedSpace.exp_add_of_commute
-- BOOK: end linear-commute

end Handbook.C25
