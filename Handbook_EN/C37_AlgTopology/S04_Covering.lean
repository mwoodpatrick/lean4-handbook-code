/- English edition source: Handbook/C37_AlgTopology/S04_Covering.lean. -/
import Mathlib

namespace Handbook.C37

-- BOOK: begin covering
-- A covering map: the fibre over each point is a stack of copies
#check @IsCoveringMap

-- Covering maps are locally homeomorphic and therefore open maps
example (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : IsCoveringMap f) : IsOpenMap f :=
  hf.isOpenMap
-- BOOK: end covering

-- BOOK: begin covering-continuous
-- The covering map is continuous (included in the definition)
example (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : IsCoveringMap f) : Continuous f :=
  hf.continuous
-- BOOK: end covering-continuous

-- BOOK: begin homology
-- Homology is formulated in the language of category theory
-- (Chapter 38)
#check @CategoryTheory.ShortComplex.homology

-- a chain complex
#check @HomologicalComplex
-- BOOK: end homology

end Handbook.C37
