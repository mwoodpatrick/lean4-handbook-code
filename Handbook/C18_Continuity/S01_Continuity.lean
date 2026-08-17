/- 第18章 関数の極限と連続性
   18.1 関数の極限 — ε-δ / 18.2 連続性 -/
import Mathlib

namespace Handbook.C18

open Topology

-- BOOK: begin cont-epsdelta
-- 連続性の定義は ε-δ と同値である(翻訳定理)
example (f : ℝ → ℝ) (a : ℝ) :
    ContinuousAt f a ↔
      ∀ ε > 0, ∃ δ > 0, ∀ x, |x - a| < δ → |f x - f a| < ε := by
  rw [Metric.continuousAt_iff]
  simp [Real.dist_eq]
-- BOOK: end cont-epsdelta

-- BOOK: begin cont-auto
-- 具体的な関数の連続性は fun_prop が自動で組み立てる
example : Continuous (fun x : ℝ => x ^ 2 + 3 * x) := by fun_prop

example : Continuous (fun x : ℝ => Real.sin (x ^ 2)) := by fun_prop
-- BOOK: end cont-auto

-- BOOK: begin cont-comp
-- 連続関数の合成・和・積はまた連続(手で組む版)
example (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => f (g x)) :=
  hf.comp hg

example (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => f x + g x) :=
  hf.add hg
-- BOOK: end cont-comp

-- BOOK: begin cont-limit
-- 点 a での連続とは「x → a のとき f x → f a」(極限=関数値)
example (f : ℝ → ℝ) (a : ℝ) (hf : ContinuousAt f a) :
    Filter.Tendsto f (𝓝 a) (𝓝 (f a)) :=
  hf.tendsto
-- BOOK: end cont-limit

end Handbook.C18
