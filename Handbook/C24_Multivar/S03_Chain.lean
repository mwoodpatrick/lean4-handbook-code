/- 第24章 多変数の微積分
   24.4 連鎖律とヤコビ行列 -/
import Mathlib

namespace Handbook.C24

-- BOOK: begin chain-sum
-- 和の全微分は全微分の和(線形写像としての和)
example (f g : ℝ × ℝ → ℝ) (f' g' : ℝ × ℝ →L[ℝ] ℝ) (x : ℝ × ℝ)
    (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) :
    HasFDerivAt (f + g) (f' + g') x :=
  hf.add hg
-- BOOK: end chain-sum

-- BOOK: begin chain-curve
-- 曲線 s ↦ (s, s²) に沿って f をたどると、
-- 変化率は「f の線形近似に速度ベクトルを代入した値」
example (f : ℝ × ℝ → ℝ) (f' : ℝ × ℝ →L[ℝ] ℝ) (t : ℝ)
    (hf : HasFDerivAt f f' (t, t ^ 2)) :
    HasDerivAt (fun s : ℝ => f (s, s ^ 2)) (f' (1, 2 * t)) t := by
  have hg : HasDerivAt (fun s : ℝ => (s, s ^ 2)) (1, 2 * t) t := by
    simpa using (hasDerivAt_id t).prodMk (hasDerivAt_pow 2 t)
  exact hf.comp_hasDerivAt t hg
-- BOOK: end chain-curve

-- BOOK: begin chain-unique
-- 全微分は一意である。だからヤコビ行列は well-defined
example (f : ℝ × ℝ → ℝ) (f' g' : ℝ × ℝ →L[ℝ] ℝ) (x : ℝ × ℝ)
    (h1 : HasFDerivAt f f' x) (h2 : HasFDerivAt f g' x) : f' = g' :=
  h1.unique h2

-- 全微分があれば連続である(1 変数と同じ含意)
example (f : ℝ × ℝ → ℝ) (f' : ℝ × ℝ →L[ℝ] ℝ) (x : ℝ × ℝ)
    (h : HasFDerivAt f f' x) : ContinuousAt f x :=
  h.continuousAt
-- BOOK: end chain-unique

end Handbook.C24
