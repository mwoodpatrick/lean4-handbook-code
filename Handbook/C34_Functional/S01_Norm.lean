/- 第34章 関数解析
   34.1 ノルム空間と Banach 空間 -/
import Mathlib

namespace Handbook.C34

open MeasureTheory

-- BOOK: begin norm-axioms
-- ノルムの公理: 三角不等式・斉次性・分離性
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
-- 逆三角不等式。ノルムが連続関数であることの根拠になる
example (E : Type) [NormedAddCommGroup E] (a b : E) :
    ‖a‖ - ‖b‖ ≤ ‖a - b‖ :=
  norm_sub_norm_le a b
-- BOOK: end norm-reverse

-- BOOK: begin banach
-- Banach 空間 = 完備なノルム空間。ℝ はその最小の例
example : CompleteSpace ℝ := by infer_instance

-- 関数の空間も Banach 空間になる(第33章の L¹)
example : CompleteSpace (Lp ℝ 1 (volume : Measure ℝ)) := by
  infer_instance

-- ノルムは距離を定める。第32章の位相がそのまま乗る
example (E : Type) [NormedAddCommGroup E] (x y : E) :
    dist x y = ‖x - y‖ :=
  dist_eq_norm x y
-- BOOK: end banach

end Handbook.C34
