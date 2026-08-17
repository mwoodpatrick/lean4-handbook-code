/- 第25章 微分方程式
   25.2 解の定義と検算 -/
import Mathlib

namespace Handbook.C25

-- BOOK: begin ode-verify
-- 解を「構成して検算する」: x(t) = C·eᵗ は x' = x を満たす
example (C : ℝ) (t : ℝ) :
    HasDerivAt (fun s => C * Real.exp s) (C * Real.exp t) t := by
  simpa using (Real.hasDerivAt_exp t).const_mul C
-- BOOK: end ode-verify

-- BOOK: begin ode-def
-- 「x が ẋ = f(t,x) の解である」は第19章の述語だけで書ける。
-- 新しい定義を導入せず、微分の言葉で完結する
def IsSolution (f : ℝ → ℝ → ℝ) (x : ℝ → ℝ) : Prop :=
  ∀ t, HasDerivAt x (f t (x t)) t

-- 上の検算はこの述語の形にそのまま収まる
example (C : ℝ) : IsSolution (fun _ x => x) (fun s => C * Real.exp s) :=
  fun t => by simpa using (Real.hasDerivAt_exp t).const_mul C
-- BOOK: end ode-def

end Handbook.C25
