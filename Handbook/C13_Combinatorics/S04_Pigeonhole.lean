/- 第13章 場合の数と確率
   13.5 鳩の巣原理 -/
import Mathlib

namespace Handbook.C13

-- BOOK: begin pigeonhole
-- 鳩の巣原理: 巣(s)より鳩(t)が多ければ、同じ巣に2羽入る
example (s t : Finset ℕ) (f : ℕ → ℕ)
    (hf : ∀ a ∈ t, f a ∈ s) (hst : s.card < t.card) :
    ∃ x ∈ t, ∃ y ∈ t, x ≠ y ∧ f x = f y :=
  Finset.exists_ne_map_eq_of_card_lt_of_maps_to hst hf
-- BOOK: end pigeonhole

end Handbook.C13
