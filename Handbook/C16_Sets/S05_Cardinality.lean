/- 第16章 集合と写像 — 数学の言語
   16.6 濃度 — 可算と非可算、Cantor の対角線論法 -/
import Mathlib

namespace Handbook.C16

-- BOOK: begin cantor
-- カントールの定理: べき集合への全射は存在しない
example (α : Type) (f : α → Set α) : ¬ Function.Surjective f :=
  Function.cantor_surjective f
-- BOOK: end cantor

-- BOOK: begin countable
-- ℕ と ℤ は同じ濃度(全単射がある)
example : Nonempty (ℕ ≃ ℤ) := ⟨(Denumerable.eqv ℤ).symm⟩

-- 実数の全体は可算でない
example : ¬ (Set.univ : Set ℝ).Countable :=
  Cardinal.not_countable_real
-- BOOK: end countable

-- BOOK: begin countable-more
-- 有理数は可算(ℕ と同じ濃度)
example : Nonempty (ℚ ≃ ℕ) := ⟨Denumerable.eqv ℚ⟩

-- ℕ×ℕ も可算 — 「無限×無限=無限」を対角線で数え上げる
example : Nonempty (ℕ × ℕ ≃ ℕ) := ⟨Denumerable.eqv (ℕ × ℕ)⟩
-- BOOK: end countable-more

end Handbook.C16
