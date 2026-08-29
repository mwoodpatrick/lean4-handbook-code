/- English edition source: Handbook/C04_Language/S01_Eval.lean. -/
import Mathlib

namespace Handbook.C04

-- BOOK: begin eval-basic
#eval 2 + 3 * 4    -- output: 14
#eval (2 + 3) * 4  -- output: 20
#eval 7 / 2        -- output: 3 (natural-number division truncates)
#eval 7 % 2        -- output: 1
-- BOOK: end eval-basic

-- BOOK: begin eval-check
-- Whereas #eval returns a "value", #check returns a "type"
#check 2 + 3               -- 2 + 3 : ℕ
#check (2 + 3 : ℤ)         -- 2 + 3 : ℤ
#check fun x : ℕ => x + 1  -- fun x => x + 1 : ℕ → ℕ
-- BOOK: end eval-check

-- BOOK: begin eval-divzero
-- Dividing by 0 raises no error (convention: x / 0 = 0)
#eval 7 / 0        -- output: 0
#eval (7 : ℚ) / 0  -- output: 0
-- BOOK: end eval-divzero

-- BOOK: begin eval-let
-- let attaches a local name to a value
#eval let s := 1 + 2 + 3 + 4; s * s      -- output: 100
#eval let x := 10; let y := x + 5; x * y -- output: 150
-- BOOK: end eval-let

end Handbook.C04
