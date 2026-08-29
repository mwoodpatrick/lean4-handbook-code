/- English edition source: Handbook/C37_AlgTopology/S03_Circle.lean. -/
import Mathlib

namespace Handbook.C37

-- BOOK: begin fta
-- The fundamental theorem of algebra: a complex polynomial of degree
-- at least 1 has a root
example (p : Polynomial ℂ) (hp : 0 < p.degree) :
    ∃ z : ℂ, p.eval z = 0 :=
  Complex.exists_root hp

-- Concrete example: x² + 1 has root i at ℂ
example : (Polynomial.X ^ 2 + 1 : Polynomial ℂ).eval Complex.I = 0 := by
  simp [Complex.I_sq]
-- BOOK: end fta

-- BOOK: begin simply-connected
-- In a simply connected space, all loops collapse to one point.
#check @SimplyConnectedSpace

-- ℝ is simply connected
example : SimplyConnectedSpace ℝ := by infer_instance

-- The circle is not simply connected: its fundamental group is ℤ
#check @Circle
-- BOOK: end simply-connected

end Handbook.C37
