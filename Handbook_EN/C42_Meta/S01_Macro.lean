/- English edition source: Handbook/C42_Meta/S01_Macro.lean. -/
import Mathlib

namespace Handbook.C42

-- BOOK: begin macro-term
-- my_double x expands to x + x
macro "my_double" x:term : term => `($x + $x)

#eval my_double 21  -- Output: 42
-- BOOK: end macro-term

-- BOOK: begin notation
-- notation introduces infix syntax; the number gives its precedence
notation:65 a " ⊕' " b => (a + b) * 2

example : (3 ⊕' 4) = 14 := by norm_num
-- BOOK: end notation

-- BOOK: begin macro-tactic
-- A tactic of one's own (a minimal example): split a conjunction
-- and close both sides with assumption
macro "easy_and" : tactic =>
  `(tactic| (constructor <;> assumption))

example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  easy_and
-- BOOK: end macro-tactic

-- BOOK: begin macro-rules
-- macro_rules adds rules to existing syntax; the number of arguments
-- can vary
syntax "triple" term : term
macro_rules
  | `(triple $x) => `($x + $x + $x)

#eval triple 7  -- Output: 21
-- BOOK: end macro-rules

end Handbook.C42
