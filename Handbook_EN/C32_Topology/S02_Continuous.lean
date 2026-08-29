/- English edition source: Handbook/C32_Topology/S02_Continuous.lean. -/
import Mathlib

namespace Handbook.C32

-- BOOK: begin cont-def
-- The definition of continuity: preimages of open sets are open
-- (the preimage of Chapter 16 takes the lead role here)
example (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) :
    Continuous f ↔ ∀ s, IsOpen s → IsOpen (f ⁻¹' s) :=
  continuous_def

-- The closed-set version: the same continuity can be stated with
-- either open or closed sets
example (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) :
    Continuous f ↔ ∀ s, IsClosed s → IsClosed (f ⁻¹' s) :=
  continuous_iff_isClosed
-- BOOK: end cont-def

-- BOOK: begin cont-comp
-- The identity and constant maps are continuous, and a composition
-- of continuous maps is continuous
example (X : Type) [TopologicalSpace X] : Continuous (id : X → X) :=
  continuous_id

example (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    (y : Y) : Continuous (fun _ : X => y) :=
  continuous_const

example (X Y Z : Type) [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (f : X → Y) (g : Y → Z)
    (hf : Continuous f) (hg : Continuous g) : Continuous (g ∘ f) :=
  hg.comp hf
-- BOOK: end cont-comp

-- BOOK: begin homeomorph
-- A homeomorphism: a continuous bijection with continuous inverse
example (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) : Continuous e ∧ Continuous e.symm :=
  ⟨e.continuous, e.symm.continuous⟩

-- under a homeomorphism the open sets correspond one to one
example (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (s : Set Y) (hs : IsOpen s) : IsOpen (e ⁻¹' s) :=
  hs.preimage e.continuous
-- BOOK: end homeomorph

end Handbook.C32
