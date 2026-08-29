/- English edition source: Handbook/C04_Language/S04_BasicTypes.lean. -/
import Mathlib

namespace Handbook.C04

-- BOOK: begin basic-sub
-- Even the same "subtraction" behaves differently depending on the type
#eval (3 - 5 : ℕ)  -- output: 0 (naturals are truncated at 0)
#eval (3 - 5 : ℤ)  -- output: -2
#eval (3 / 4 : ℚ)  -- output: 3/4
-- BOOK: end basic-sub

-- BOOK: begin basic-bool
-- Bool is the truth value of the computational world.
-- Propositions (Prop) cannot be #eval'd; decide reduces them to Bool
-- for computation.
#eval decide (2 < 3)  -- output: true
#eval decide (3 ∣ 12) -- output: true
-- BOOK: end basic-bool

-- BOOK: begin basic-list
#eval "Lean " ++ "4"           -- output: "Lean 4"
#eval [1, 2, 3].map (· * 2)    -- output: [2, 4, 6]
#eval (List.range 5).sum       -- output: 10
-- BOOK: end basic-list

-- BOOK: begin basic-float
-- Float is the world of approximation. 0.1 + 0.2 does not equal 0.3.
#eval (0.1 + 0.2 : Float)         -- output: 0.300000000000000044
#eval (0.1 + 0.2 : Float) == 0.3  -- output: false
#eval (1 / 10 + 2 / 10 : ℚ)       -- over ℚ it is exactly 3/10
-- BOOK: end basic-float

-- BOOK: begin basic-coe
-- We move from a narrower type to a wider one with ↑ (coercion)
#check ((3 : ℕ) : ℤ)     -- ↑3 : ℤ
#eval ((3 : ℕ) : ℚ) / 4  -- output: 3/4 (move into ℚ first, then divide)

-- Equalities that cross coercions are tidied up with push_cast
example (m n : ℕ) : ((m + n : ℕ) : ℤ) = m + n := by
  push_cast; ring
-- BOOK: end basic-coe

end Handbook.C04
