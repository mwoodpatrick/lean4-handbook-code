/- 第18章 関数の極限と連続性
   18.1 関数の極限 / 18.2 片側極限 / 18.6 数列による特徴づけ -/
import Mathlib

open Filter Topology

namespace Handbook.C18

-- BOOK: begin flimit-def
-- 関数の極限の ε-δ 翻訳。δ が ε ごとに取れることを言う
#check @Metric.tendsto_nhds_nhds

-- lim_{x→2} (3x + 1) = 7
example : Tendsto (fun x : ℝ => 3 * x + 1) (𝓝 2) (𝓝 7) := by
  have h : Continuous (fun x : ℝ => 3 * x + 1) := by fun_prop
  have := h.tendsto 2
  norm_num at this
  exact this
-- BOOK: end flimit-def

-- BOOK: begin flimit-punctured
-- 𝓝[≠] a は「a を除いた近傍」。x = a を除外する古典的な定義
#check @Metric.tendsto_nhdsWithin_nhds

-- 除外つきの極限。𝓝 a より弱い条件なので、こちらは成立しやすい
example (f : ℝ → ℝ) (a L : ℝ) (h : Tendsto f (𝓝 a) (𝓝 L)) :
    Tendsto f (𝓝[≠] a) (𝓝 L) :=
  h.mono_left nhdsWithin_le_nhds
-- BOOK: end flimit-punctured

-- BOOK: begin flimit-alg
-- 極限の四則。フィルタ側は何でもよいので数列にも関数にも効く
#check @Filter.Tendsto.add

-- 商だけは分母の極限が 0 でないという仮定が要る
#check @Filter.Tendsto.div
-- BOOK: end flimit-alg

-- BOOK: begin onesided
-- 片側極限は定義域を Ioi a(右側)に制限した連続性で書く
example (f : ℝ → ℝ) (a : ℝ) :
    ContinuousWithinAt f (Set.Ioi a) a ↔
      ContinuousWithinAt f (Set.Ici a) a :=
  continuousWithinAt_Ioi_iff_Ici
-- BOOK: end onesided

-- BOOK: begin seq-cont
-- 連続性は「収束列を収束列へ写す」ことと同値(ℝ では)
example (f : ℝ → ℝ) (h : Continuous f) : SeqContinuous f :=
  continuous_iff_seqContinuous.mp h

-- フィルタ版。可算生成のフィルタなら数列で判定してよい
#check @Filter.tendsto_iff_seq_tendsto
-- BOOK: end seq-cont

end Handbook.C18
