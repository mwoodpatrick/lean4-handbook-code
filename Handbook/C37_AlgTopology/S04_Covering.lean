/- 第37章 代数的トポロジー
   37.4 被覆空間 / 37.5 ホモロジーへの一瞥 -/
import Mathlib

namespace Handbook.C37

-- BOOK: begin covering
-- 被覆写像: 各点のまわりが「同じものの積み重ね」に見える写像
#check @IsCoveringMap

-- 被覆写像は局所同相であり、したがって開写像である
example (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : IsCoveringMap f) : IsOpenMap f :=
  hf.isOpenMap
-- BOOK: end covering

-- BOOK: begin covering-continuous
-- 被覆写像は連続である(定義に含まれる)
example (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : IsCoveringMap f) : Continuous f :=
  hf.continuous
-- BOOK: end covering-continuous

-- BOOK: begin homology
-- ホモロジーは圏論的に定式化されている(第38章)
#check @CategoryTheory.ShortComplex.homology

-- 鎖複体
#check @HomologicalComplex
-- BOOK: end homology

end Handbook.C37
