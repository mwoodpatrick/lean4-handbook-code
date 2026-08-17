/- 第25章 微分方程式
   25.6 一意性と Gronwall の不等式 -/
import Mathlib

open Set

namespace Handbook.C25

-- BOOK: begin unique-exist
-- Picard–Lindelöf の仮定一式は構造体にまとまっている
#check @IsPicardLindelof

-- 存在定理: 仮定を満たせば区間上の解が構成できる
#check @IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt
-- BOOK: end unique-exist

-- BOOK: begin unique-main
-- 一意性: v が Lipschitz なら、初期値の一致する2解は区間上で一致する
example {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : ℝ → E → E) (K : NNReal) (f g : ℝ → E) (a b : ℝ)
    (hv : ∀ t, LipschitzWith K (v t))
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ico a b, HasDerivWithinAt f (v t (f t)) (Ici t) t)
    (hg : ContinuousOn g (Icc a b))
    (hg' : ∀ t ∈ Ico a b, HasDerivWithinAt g (v t (g t)) (Ici t) t)
    (ha : f a = g a) : EqOn f g (Icc a b) :=
  ODE_solution_unique hv hf hf' hg hg' ha
-- BOOK: end unique-main

-- BOOK: begin unique-gronwall
-- Gronwall の不等式。誤差が自分自身に比例して増えるとき、
-- 増え方は指数関数で抑えられる
#check @gronwallBound
#check @norm_le_gronwallBound_of_norm_deriv_right_le
-- BOOK: end unique-gronwall

-- BOOK: begin unique-dist
-- 初期値がずれた2本の軌道の距離も指数関数で抑えられる。
-- これが解の初期値への連続依存性である
#check @dist_le_of_trajectories_ODE
-- BOOK: end unique-dist

end Handbook.C25
