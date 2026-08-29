/- English edition source: Handbook/C37_AlgTopology/S02_FundGroup.lean. -/
import Mathlib

namespace Handbook.C37

-- BOOK: begin fundamental-group
-- Fundamental group: the group of homotopy classes of centered loops
#check @FundamentalGroup

-- that it is a group is supplied as a type class instance
noncomputable example (X : Type) [TopologicalSpace X] (x : X) :
    Group (FundamentalGroup X x) := by
  infer_instance
-- BOOK: end fundamental-group

-- BOOK: begin fundamental-groupoid
-- The version without a fixed base point is the fundamental groupoid;
-- the automorphisms of one object form the fundamental group.
#check @FundamentalGroupoid

-- Simply connected: the fundamental group is trivial
#check @SimplyConnectedSpace

-- ℝ is path-connected
example : PathConnectedSpace ℝ := by infer_instance
-- BOOK: end fundamental-groupoid

end Handbook.C37
