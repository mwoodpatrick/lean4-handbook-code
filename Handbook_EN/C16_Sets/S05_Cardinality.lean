/- English edition source: Handbook/C16_Sets/S05_Cardinality.lean. -/
import Mathlib

namespace Handbook.C16

-- BOOK: begin cantor
-- Cantor’s theorem: there is no surjection onto the power set
example (α : Type) (f : α → Set α) : ¬ Function.Surjective f :=
  Function.cantor_surjective f
-- BOOK: end cantor

-- BOOK: begin countable
-- ℕ and ℤ have the same cardinality (there is a bijection)
example : Nonempty (ℕ ≃ ℤ) := ⟨(Denumerable.eqv ℤ).symm⟩

-- The real numbers are uncountable
example : ¬ (Set.univ : Set ℝ).Countable :=
  Cardinal.not_countable_real
-- BOOK: end countable

-- BOOK: begin countable-more
-- The rationals are countable (the same cardinality as ℕ)
example : Nonempty (ℚ ≃ ℕ) := ⟨Denumerable.eqv ℚ⟩

-- ℕ×ℕ is countable too --- enumerate “infinity × infinity = infinity”
-- diagonally
example : Nonempty (ℕ × ℕ ≃ ℕ) := ⟨Denumerable.eqv (ℕ × ℕ)⟩
-- BOOK: end countable-more

end Handbook.C16
