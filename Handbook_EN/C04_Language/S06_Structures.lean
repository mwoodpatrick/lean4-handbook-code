/- English edition source: Handbook/C04_Language/S06_Structures.lean. -/
import Mathlib

namespace Handbook.C04

-- BOOK: begin struct-point
-- A structure is a bundle of fields
structure Point where
  x : ℚ
  y : ℚ
  deriving Repr

def p : Point := ⟨1, 2⟩

#eval p.x + p.y  -- output: 3
-- BOOK: end struct-point

-- BOOK: begin struct-class
-- Type class: endows a type with the ability of "having a measurable
-- size"
class HasSize (α : Type) where
  size : α → ℚ

instance : HasSize Point where
  size q := |q.x| + |q.y|

#eval HasSize.size p  -- output: 3
-- BOOK: end struct-class

-- BOOK: begin struct-update
-- The with syntax: build a new value that changes only some fields
def q : Point := { p with y := 5 }

#eval q  -- output: { x := 1, y := 5 }
#eval p  -- output: { x := 1, y := 2 } (the original p is unchanged)
-- BOOK: end struct-update

end Handbook.C04
