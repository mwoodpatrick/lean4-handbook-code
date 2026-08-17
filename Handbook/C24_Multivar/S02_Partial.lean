/- 第24章 多変数の微積分
   24.2 偏微分と方向微分 -/
import Mathlib

namespace Handbook.C24

-- BOOK: begin partial-slice
-- y を b に固定した断面 t ↦ t·b は 1 変数関数。
-- その微分係数 b が、f(x,y)=xy の x 偏微分である
example (b x : ℝ) : HasDerivAt (fun t : ℝ => t * b) b x := by
  simpa using (hasDerivAt_id x).mul_const b
-- BOOK: end partial-slice

-- BOOK: begin partial-product
-- f(x,y) = xy の全微分。(a,b) での係数がそのまま
-- 2 つの偏微分 ∂f/∂x = b, ∂f/∂y = a になっている
example (a b : ℝ) :
    HasFDerivAt (fun p : ℝ × ℝ => p.1 * p.2)
      (a • ContinuousLinearMap.snd ℝ ℝ ℝ
        + b • ContinuousLinearMap.fst ℝ ℝ ℝ) (a, b) := by
  -- 積の微分法則。点 (a,b) を明示しないと単一化に失敗する
  have h := (hasFDerivAt_fst (𝕜 := ℝ) (p := (a, b))).mul
    (hasFDerivAt_snd (𝕜 := ℝ) (p := (a, b)))
  exact h
-- BOOK: end partial-product

-- BOOK: begin line-deriv
-- 方向微分: 点 x から方向 v へ動いたときの変化率
#check @lineDeriv

-- 全微分があれば、どの方向 v の方向微分も存在し、
-- その値は線形写像 L に v を代入した L v である
example (f : ℝ × ℝ → ℝ) (L : ℝ × ℝ →L[ℝ] ℝ) (x v : ℝ × ℝ)
    (hf : HasFDerivAt f L x) : HasLineDerivAt ℝ f (L v) x v :=
  hf.hasLineDerivAt v
-- BOOK: end line-deriv

-- BOOK: begin line-deriv-zero
-- 方向微分が存在しないとき lineDeriv は 0 を返す(規約値)。
-- 「0 が返った」だけでは変化率が 0 とは言えない
#check @lineDeriv_zero_of_not_lineDifferentiableAt
-- BOOK: end line-deriv-zero

end Handbook.C24
