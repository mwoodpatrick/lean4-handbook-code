/- 第34章 関数解析
   34.6 スペクトル入門 -/
import Mathlib

namespace Handbook.C34

-- BOOK: begin spectrum-def
-- スペクトル: a - μ が可逆にならない μ の全体。固有値の一般化
example (A : Type) [NormedRing A] [NormedAlgebra ℂ A] (a : A) :
    spectrum ℂ a = {μ : ℂ | ¬IsUnit (algebraMap ℂ A μ - a)} :=
  rfl
-- BOOK: end spectrum-def

-- BOOK: begin spectrum-nonempty
-- 複素 Banach 環ではスペクトルが必ず空でない(Gelfand)
example (A : Type) [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] [Nontrivial A] (a : A) :
    (spectrum ℂ a).Nonempty :=
  spectrum.nonempty a
-- BOOK: end spectrum-nonempty

-- BOOK: begin spectrum-bounded
-- スペクトルは半径 ‖a‖ の閉円板に収まる。有界かつ空でない
example (A : Type) [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] [NormOneClass A] (a : A) :
    spectrum ℂ a ⊆ Metric.closedBall 0 ‖a‖ :=
  spectrum.subset_closedBall_norm a
-- BOOK: end spectrum-bounded

end Handbook.C34
