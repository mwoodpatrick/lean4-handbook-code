/- English edition source: Handbook/C18_Continuity/S03_Max.lean. -/
import Mathlib

namespace Handbook.C18

-- BOOK: begin max-value
-- Extreme value theorem: a continuous function on a closed interval
-- attains a maximum
-- (IsMaxOn f s x says that x is a maximum point of f on s)
example (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc 0 1)) :
    ∃ x ∈ Set.Icc (0 : ℝ) 1, IsMaxOn f (Set.Icc 0 1) x :=
  IsCompact.exists_isMaxOn isCompact_Icc
    (Set.nonempty_Icc.mpr (by norm_num)) hf
-- BOOK: end max-value

-- BOOK: begin heine
-- Heine's theorem: on a compact set, continuity implies uniform
-- continuity
example (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc 0 1)) :
    UniformContinuousOn f (Set.Icc 0 1) :=
  IsCompact.uniformContinuousOn_of_continuous isCompact_Icc hf
-- BOOK: end heine

-- BOOK: begin min-value
-- The minimum as well (compactness plus continuity)
example (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc 0 1)) :
    ∃ x ∈ Set.Icc (0 : ℝ) 1, IsMinOn f (Set.Icc 0 1) x :=
  IsCompact.exists_isMinOn isCompact_Icc
    (Set.nonempty_Icc.mpr (by norm_num)) hf
-- BOOK: end min-value

end Handbook.C18
