/- Chapter 40: Finding your way around mathlib
   40.2 Naming conventions -/
import Mathlib

namespace Handbook.C40

-- BOOK: begin naming-read
-- Read the conclusion off from the left and the name appears
#check @Nat.add_comm      -- add is comm
#check @mul_pos           -- mul is pos
#check @abs_add_le        -- abs of add is le
#check @add_mul           -- add then mul (distributivity)
-- BOOK: end naming-read

-- BOOK: begin naming-dot
-- Dot notation fills the first argument from the namespace
example {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] {f : X → Y} {g : Y → Z}
    (hg : Continuous g) (hf : Continuous f) :
    Continuous (g ∘ f) :=
  hg.comp hf
-- BOOK: end naming-dot

-- BOOK: begin naming-direction
-- "of" means "from the hypotheses on the right"
example (a b : ℝ) (h : a < b) : a ≤ b := le_of_lt h

-- an iff is used in either direction with .mp and .mpr
example (n m : ℕ) (h : n ≤ m) : n < m + 1 :=
  Nat.lt_succ_iff.mpr h

-- two candidates differing in their hypotheses
#check @mul_le_mul_right
#check @mul_le_mul_of_nonneg_right
-- BOOK: end naming-direction

end Handbook.C40
