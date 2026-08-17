/- 第33章 測度論とルベーグ積分
   33.2 σ-加法族と可測関数 -/
import Mathlib

namespace Handbook.C33

open MeasureTheory

-- BOOK: begin sigma-axioms
-- σ-加法族の3公理: 全体・補集合・可算合併で閉じる
example (α : Type) [MeasurableSpace α] :
    MeasurableSet (Set.univ : Set α) :=
  MeasurableSet.univ

example (α : Type) [MeasurableSpace α] (s : Set α)
    (hs : MeasurableSet s) : MeasurableSet sᶜ :=
  hs.compl

-- 合併は「可算個」まで。位相の「任意個」との違いが要点
example (α : Type) [MeasurableSpace α] (f : ℕ → Set α)
    (hf : ∀ n, MeasurableSet (f n)) : MeasurableSet (⋃ n, f n) :=
  MeasurableSet.iUnion hf
-- BOOK: end sigma-axioms

-- BOOK: begin measurable-fun
-- 可測関数: 可測集合の逆像が可測(連続の定義と同じ形)
example (α : Type) [MeasurableSpace α] (c : ℝ) :
    Measurable (fun _ : α => c) :=
  measurable_const

example (f g : ℝ → ℝ) (hf : Measurable f) (hg : Measurable g) :
    Measurable (g ∘ f) :=
  hg.comp hf

-- 連続ならば可測。開集合が可測集合を生成するため
example (f : ℝ → ℝ) (hf : Continuous f) : Measurable f :=
  hf.measurable
-- BOOK: end measurable-fun

end Handbook.C33
