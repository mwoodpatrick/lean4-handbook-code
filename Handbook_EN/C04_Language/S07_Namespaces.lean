/- English edition source: Handbook/C04_Language/S07_Namespaces.lean. -/
import Mathlib

namespace Handbook.C04

-- BOOK: begin ns-basic
namespace Geometry

def area (w h : ℚ) : ℚ := w * h

end Geometry

#eval Geometry.area 3 4  -- output: 12

open Geometry in
#eval area 5 6           -- output: 30
-- BOOK: end ns-basic

-- BOOK: begin ns-dot
-- The namespace of the first argument's type can be called with "dot
-- notation"
#eval (6 : ℕ).gcd 4      -- output: 2 (same as Nat.gcd 6 4)
#eval [3, 1, 2].reverse  -- output: [2, 1, 3] (List.reverse)
-- BOOK: end ns-dot

-- BOOK: begin ns-open
-- open brings the contents of a namespace into the current scope
open Real in
#check sqrt 2  -- Real.sqrt 2 : ℝ (after open we can call it "sqrt")

section
open List in
#eval range 4  -- output: [0, 1, 2, 3]
end
-- BOOK: end ns-open

end Handbook.C04
