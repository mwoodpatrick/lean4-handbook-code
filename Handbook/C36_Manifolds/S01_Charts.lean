/- 第36章 多様体
   36.2 チャート・アトラス・可微分構造 -/
import Mathlib

namespace Handbook.C36

open Manifold

-- BOOK: begin charted-space
-- チャート付き空間: 各点のまわりがモデル空間と同相
#check @ChartedSpace

-- ℝ 自身は自明なチャート付き空間(チャートは恒等写像1枚)
example : ChartedSpace ℝ ℝ := by infer_instance

-- 各点にチャートが割り当てられる。値は開部分同相写像
example (x : ℝ) : OpenPartialHomeomorph ℝ ℝ := chartAt ℝ x
-- BOOK: end charted-space

-- BOOK: begin chart-inverse
-- チャートは同相なので逆も取れる。行き来が「座標変換」になる
example (x : ℝ) : OpenPartialHomeomorph ℝ ℝ := (chartAt ℝ x).symm

-- 円周 S¹ もチャート付き空間。1枚では覆えず、複数枚が要る
noncomputable example :
    ChartedSpace (EuclideanSpace ℝ (Fin 1))
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) := by
  infer_instance
-- BOOK: end chart-inverse

end Handbook.C36
