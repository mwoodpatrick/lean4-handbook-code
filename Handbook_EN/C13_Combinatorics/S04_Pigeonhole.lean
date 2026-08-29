/- English edition source: Handbook/C13_Combinatorics/S04_Pigeonhole.lean. -/
import Mathlib

namespace Handbook.C13

-- BOOK: begin pigeonhole
-- Pigeonhole principle: if there are more pigeons (t) than holes (s),
-- two occupy the same hole
example (s t : Finset ℕ) (f : ℕ → ℕ)
    (hf : ∀ a ∈ t, f a ∈ s) (hst : s.card < t.card) :
    ∃ x ∈ t, ∃ y ∈ t, x ≠ y ∧ f x = f y :=
  Finset.exists_ne_map_eq_of_card_lt_of_maps_to hst hf
-- BOOK: end pigeonhole

end Handbook.C13
