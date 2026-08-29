/- English edition source: Handbook/C34_Functional/S01_Norm.lean. -/
import Mathlib

namespace Handbook.C34

open MeasureTheory

-- BOOK: begin norm-axioms
-- The axioms of a norm: the triangle inequality, homogeneity,
-- and vanishing only at 0
example (E : Type) [NormedAddCommGroup E] (x y : E) :
    ‖x + y‖ ≤ ‖x‖ + ‖y‖ :=
  norm_add_le x y

example (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (x : E) : ‖c • x‖ = |c| * ‖x‖ := by
  rw [norm_smul, Real.norm_eq_abs]

example (E : Type) [NormedAddCommGroup E] (x : E) :
    ‖x‖ = 0 ↔ x = 0 :=
  norm_eq_zero
-- BOOK: end norm-axioms

-- BOOK: begin norm-reverse
-- The reverse triangle inequality, the ground for continuity of
-- the norm
example (E : Type) [NormedAddCommGroup E] (a b : E) :
    ‖a‖ - ‖b‖ ≤ ‖a - b‖ :=
  norm_sub_norm_le a b
-- BOOK: end norm-reverse

-- BOOK: begin banach
-- A Banach space is a complete normed space; ℝ is the smallest
-- example
example : CompleteSpace ℝ := by infer_instance

-- function spaces are Banach spaces too (the L¹ of Chapter 33)
example : CompleteSpace (Lp ℝ 1 (volume : Measure ℝ)) := by
  infer_instance

-- A norm determines a distance (Chapter 32)
example (E : Type) [NormedAddCommGroup E] (x y : E) :
    dist x y = ‖x - y‖ :=
  dist_eq_norm x y
-- BOOK: end banach

end Handbook.C34
