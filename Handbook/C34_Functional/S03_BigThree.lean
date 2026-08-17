/- 第34章 関数解析
   34.3 三大定理 -/
import Mathlib

namespace Handbook.C34

-- BOOK: begin hahn-banach
-- Hahn–Banach: 部分空間上の汎関数をノルムを保って全体へ延長できる
example (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : Subspace ℝ E) (f : StrongDual ℝ p) :
    ∃ g : StrongDual ℝ E, (∀ x : p, g x = f x) ∧ ‖g‖ = ‖f‖ :=
  exists_extension_norm_eq p f
-- BOOK: end hahn-banach

-- BOOK: begin uniform-bounded
-- 一様有界性原理: 各点で有界なら作用素ノルムが一様に有界
example (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace E]
    (ι : Type) (g : ι → E →L[ℝ] F)
    (h : ∀ x, ∃ C, ∀ i, ‖g i x‖ ≤ C) :
    ∃ C', ∀ i, ‖g i‖ ≤ C' :=
  banach_steinhaus h
-- BOOK: end uniform-bounded

-- BOOK: begin open-mapping
-- 開写像定理: 全射な有界線形作用素は開写像である
#check @ContinuousLinearMap.isOpenMap

-- 系として、全単射な有界線形作用素の逆も有界(逆写像定理)
#check @ContinuousLinearEquiv.ofBijective
-- BOOK: end open-mapping

end Handbook.C34
