/- 第24章 多変数の微積分
   24.3 全微分 fderiv — 微分とは線形近似である -/
import Mathlib

namespace Handbook.C24

-- BOOK: begin fderiv
-- 全微分は「連続線形写像による最良近似」
#check @fderiv

-- 第1成分を取る写像の全微分は、第1成分を取る線形写像そのもの
example (p : ℝ × ℝ) :
    HasFDerivAt Prod.fst (ContinuousLinearMap.fst ℝ ℝ ℝ) p :=
  hasFDerivAt_fst
-- BOOK: end fderiv

-- BOOK: begin fderiv-defn
-- 定義の正体: f(x+h) - f(x) - f'(h) が ‖h‖ より速く 0 へ行く
#check @hasFDerivAt_iff_isLittleO

-- 商の形で書いた同値な条件(1変数の定義に近い見た目)
#check @hasFDerivAt_iff_tendsto
-- BOOK: end fderiv-defn

-- BOOK: begin fderiv-basic
-- 定数写像の全微分は 0(どの方向にも変化しない)
example (c : ℝ) (x : ℝ × ℝ) :
    HasFDerivAt (fun _ : ℝ × ℝ => c) (0 : ℝ × ℝ →L[ℝ] ℝ) x :=
  hasFDerivAt_const c x

-- 恒等写像の全微分は恒等線形写像
example (x : ℝ × ℝ) :
    HasFDerivAt id (ContinuousLinearMap.id ℝ (ℝ × ℝ)) x :=
  hasFDerivAt_id x
-- BOOK: end fderiv-basic

-- BOOK: begin fderiv-bridge
-- 1変数の HasDerivAt は HasFDerivAt の特殊化(c 倍の線形写像)
example (f : ℝ → ℝ) (c x : ℝ) :
    HasDerivAt f c x ↔
      HasFDerivAt f (ContinuousLinearMap.toSpanSingleton ℝ c) x :=
  hasDerivAt_iff_hasFDerivAt
-- BOOK: end fderiv-bridge

-- BOOK: begin fderiv-chain
-- 連鎖律: 合成の全微分は全微分の合成
example (f : ℝ × ℝ → ℝ) (g : ℝ → ℝ × ℝ) (x : ℝ)
    (f' : ℝ × ℝ →L[ℝ] ℝ) (g' : ℝ →L[ℝ] ℝ × ℝ)
    (hf : HasFDerivAt f f' (g x)) (hg : HasFDerivAt g g' x) :
    HasFDerivAt (f ∘ g) (f'.comp g') x :=
  hf.comp x hg
-- BOOK: end fderiv-chain

end Handbook.C24
