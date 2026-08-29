/- English edition source: Handbook/C33_Measure/S01_Sigma.lean. -/
import Mathlib

namespace Handbook.C33

open MeasureTheory

-- BOOK: begin sigma-axioms
-- The three axioms of a σ-algebra: it contains the whole space and
-- is closed under complements and countable unions
example (α : Type) [MeasurableSpace α] :
    MeasurableSet (Set.univ : Set α) :=
  MeasurableSet.univ

example (α : Type) [MeasurableSpace α] (s : Set α)
    (hs : MeasurableSet s) : MeasurableSet sᶜ :=
  hs.compl

-- Unions are countable only. The difference from the topology's
-- "arbitrary" unions is essential.
example (α : Type) [MeasurableSpace α] (f : ℕ → Set α)
    (hf : ∀ n, MeasurableSet (f n)) : MeasurableSet (⋃ n, f n) :=
  MeasurableSet.iUnion hf
-- BOOK: end sigma-axioms

-- BOOK: begin measurable-fun
-- A measurable function: preimages of measurable sets are measurable
-- (the same shape as the definition of continuity)
example (α : Type) [MeasurableSpace α] (c : ℝ) :
    Measurable (fun _ : α => c) :=
  measurable_const

example (f g : ℝ → ℝ) (hf : Measurable f) (hg : Measurable g) :
    Measurable (g ∘ f) :=
  hg.comp hf

-- A continuous function is measurable, because the open sets
-- generate the Borel σ-algebra
example (f : ℝ → ℝ) (hf : Continuous f) : Measurable f :=
  hf.measurable
-- BOOK: end measurable-fun

end Handbook.C33
