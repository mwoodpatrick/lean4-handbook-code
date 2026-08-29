/- English edition source: Handbook/C16_Sets/S06_Choice.lean. -/
import Mathlib

namespace Handbook.C16

-- BOOK: begin choice
-- Classical.choice: the axiom that extracts “the value itself” from
-- “there exists”
#check @Classical.choice  -- Nonempty α → α

-- It cannot compute, so it is marked noncomputable
noncomputable def pick (α : Type) (h : Nonempty α) : α :=
  Classical.choice h
-- BOOK: end choice

end Handbook.C16
