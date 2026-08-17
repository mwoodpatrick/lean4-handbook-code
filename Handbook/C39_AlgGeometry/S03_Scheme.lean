/- 第39章 代数幾何入門
   39.4 層とスキーム -/
import Mathlib

namespace Handbook.C39

-- BOOK: begin scheme
-- スキーム: 現代代数幾何の基礎概念が完全形式化されている
#check @AlgebraicGeometry.Scheme

-- Spec 関手: 可換環からアフィンスキームを作る
#check @AlgebraicGeometry.Spec
-- BOOK: end scheme

-- BOOK: begin localization
-- 局所化: f を可逆にした環。構造層が D(f) に載せる環がこれ
#check @Localization.Away

-- ℤ を 2 で局所化すると ℤ[1/2]。分母が 2 のべきの有理数全体
example : CommRing (Localization.Away (2 : ℤ)) := by
  infer_instance
-- BOOK: end localization

-- BOOK: begin sheaf
-- 層は「開集合の圏から環の圏への反変関手」(第38章)
#check @TopologicalSpace.Opens

-- 開集合全体は包含関係で順序集合をなし、圏と見なせる
example (X : Type) [TopologicalSpace X] :
    PartialOrder (TopologicalSpace.Opens X) :=
  inferInstance
-- BOOK: end sheaf

end Handbook.C39
