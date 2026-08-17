/- 第27章 確率論の基礎
   27.5 期待値と分散 / 27.7 大数の法則 -/
import Mathlib

namespace Handbook.C27

open MeasureTheory ProbabilityTheory

-- BOOK: begin expect-def
-- 期待値は積分そのもの。第33章のルベーグ積分をそのまま使う
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) :
    μ[X] = ∫ ω, X ω ∂μ :=
  rfl
-- BOOK: end expect-def

-- BOOK: begin variance-def
-- 分散は「平均からのずれの2乗」の期待値
example {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}
    (hX : AEMeasurable X μ) :
    Var[X; μ] = ∫ ω, (X ω - μ[X]) ^ 2 ∂μ :=
  variance_eq_integral hX

-- 分散は非負(平方の積分だから)
example {Ω : Type} [MeasurableSpace Ω] (X : Ω → ℝ) (μ : Measure Ω) :
    0 ≤ Var[X; μ] :=
  variance_nonneg X μ
-- BOOK: end variance-def

-- BOOK: begin variance-scale
-- 定数倍すると分散は2乗倍になる(標準偏差なら c 倍)
#check @ProbabilityTheory.variance_const_mul

-- E[X²] - E[X]² という計算しやすい形
#check @ProbabilityTheory.variance_eq_sub
-- BOOK: end variance-scale

-- BOOK: begin chebyshev
-- チェビシェフの不等式: 平均から c 以上ずれる確率は Var/c² 以下。
-- 分布の形を一切仮定せずに裾を評価できる
#check @ProbabilityTheory.meas_ge_le_variance_div_sq
-- BOOK: end chebyshev

-- BOOK: begin strong-law
-- 大数の強法則: 独立同分布なら標本平均は期待値へ概収束する
#check @ProbabilityTheory.strong_law_ae
-- BOOK: end strong-law

end Handbook.C27
