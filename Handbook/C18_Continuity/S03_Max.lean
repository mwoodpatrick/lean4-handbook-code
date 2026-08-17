/- 第18章 関数の極限と連続性
   18.4 最大値の定理 / 18.5 一様連続性 -/
import Mathlib

namespace Handbook.C18

-- BOOK: begin max-value
-- 最大値の定理: 閉区間上の連続関数は最大値を取る
-- (IsMaxOn f s x は「x が s 上の最大点」)
example (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc 0 1)) :
    ∃ x ∈ Set.Icc (0 : ℝ) 1, IsMaxOn f (Set.Icc 0 1) x :=
  IsCompact.exists_isMaxOn isCompact_Icc
    (Set.nonempty_Icc.mpr (by norm_num)) hf
-- BOOK: end max-value

-- BOOK: begin heine
-- ハイネの定理: コンパクト集合上では連続なら一様連続
example (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc 0 1)) :
    UniformContinuousOn f (Set.Icc 0 1) :=
  IsCompact.uniformContinuousOn_of_continuous isCompact_Icc hf
-- BOOK: end heine

-- BOOK: begin min-value
-- 最小値も同様に取る(コンパクト+連続)
example (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc 0 1)) :
    ∃ x ∈ Set.Icc (0 : ℝ) 1, IsMinOn f (Set.Icc 0 1) x :=
  IsCompact.exists_isMinOn isCompact_Icc
    (Set.nonempty_Icc.mpr (by norm_num)) hf
-- BOOK: end min-value

end Handbook.C18
