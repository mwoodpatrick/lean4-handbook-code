/- 第19章 微分
   19.1 微分係数の定義 / 19.2 計算規則 -/
import Mathlib

namespace Handbook.C19

-- BOOK: begin deriv-def
-- HasDerivAt f c x: f は点 x で微分係数 c を持つ
example : HasDerivAt (fun x : ℝ => x ^ 2) 6 3 := by
  have h := hasDerivAt_pow 2 (3 : ℝ)
  norm_num at h
  exact h

-- deriv は「微分係数を返す関数」
example : deriv (fun x : ℝ => x ^ 2) 3 = 6 := by
  norm_num [deriv_pow]
-- BOOK: end deriv-def

-- BOOK: begin deriv-rules
-- 積の微分(ライプニッツ則)
example (f g : ℝ → ℝ) (x : ℝ)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    deriv (fun y => f y * g y) x
      = deriv f x * g x + f x * deriv g x :=
  deriv_mul hf hg

-- 連鎖律(合成関数の微分)
example (f g : ℝ → ℝ) (x : ℝ)
    (hg : DifferentiableAt ℝ g x)
    (hf : DifferentiableAt ℝ f (g x)) :
    deriv (f ∘ g) x = deriv f (g x) * deriv g x :=
  deriv_comp x hf hg
-- BOOK: end deriv-rules

-- BOOK: begin deriv-basic
-- 基本の微分公式(定数・恒等・べき)
example (c : ℝ) : deriv (fun _ : ℝ => c) = fun _ => 0 := by
  funext x; simp

example : deriv (fun x : ℝ => x) = fun _ => 1 := by
  funext x; simp

-- (xⁿ)' = n xⁿ⁻¹
example (n : ℕ) (x : ℝ) :
    deriv (fun y : ℝ => y ^ n) x = n * x ^ (n - 1) := by
  simp
-- BOOK: end deriv-basic

-- BOOK: begin deriv-add
-- 和の微分は微分の和
example (f g : ℝ → ℝ) (x : ℝ)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    deriv (fun y => f y + g y) x = deriv f x + deriv g x :=
  deriv_add hf hg
-- BOOK: end deriv-add

end Handbook.C19
