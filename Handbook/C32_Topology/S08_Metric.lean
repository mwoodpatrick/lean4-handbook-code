/- 第32章 位相空間論
   32.8 距離空間と位相の関係・完備化 -/
import Mathlib

namespace Handbook.C32

-- BOOK: begin metric-topo
-- 距離空間の位相: 開集合とは「各点に開球が入る集合」
example (X : Type) [MetricSpace X] (s : Set X) :
    IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, Metric.ball x ε ⊆ s :=
  Metric.isOpen_iff

-- 開球そのものは開集合である
example (X : Type) [MetricSpace X] (x : X) (ε : ℝ) :
    IsOpen (Metric.ball x ε) :=
  Metric.isOpen_ball
-- BOOK: end metric-topo

-- BOOK: begin metric-complete
-- ℝ は完備。ℚ を完備化して得た空間だという事実の形式版
example : CompleteSpace ℝ := by infer_instance

-- ℝ はハウスドルフでもある(距離空間はすべて T₂)
example : T2Space ℝ := by infer_instance
-- BOOK: end metric-complete

-- BOOK: begin cauchy
-- コーシー列: 番号を大きくすると項どうしが近づく列
example (u : ℕ → ℝ) :
    CauchySeq u
      ↔ ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, dist (u m) (u n) < ε :=
  Metric.cauchySeq_iff

-- 完備性の中身: コーシー列には必ず行き先がある
example (u : ℕ → ℝ) (hu : CauchySeq u) :
    ∃ x, Filter.Tendsto u Filter.atTop (nhds x) :=
  cauchySeq_tendsto_of_complete hu
-- BOOK: end cauchy

-- BOOK: begin completion
-- 任意の一様空間に完備化が構成できる。ℚ の完備化は完備な空間
example : CompleteSpace (UniformSpace.Completion ℚ) := by
  infer_instance

-- 元の空間は完備化の中に稠密に埋め込まれる
example (X : Type) [MetricSpace X] :
    DenseRange ((↑) : X → UniformSpace.Completion X) :=
  UniformSpace.Completion.denseRange_coe
-- BOOK: end completion

end Handbook.C32
