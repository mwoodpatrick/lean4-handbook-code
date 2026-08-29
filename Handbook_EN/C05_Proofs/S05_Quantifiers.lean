/- Chapter 5: The fundamentals of proof
   5.5 Universal and existential quantifiers -/
import Mathlib

namespace Handbook.C05

-- BOOK: begin quant-forall
-- To show a ∀, take an arbitrary element with intro
example : ∀ n : ℕ, 0 ≤ n := by
  intro n
  exact Nat.zero_le n

-- a ∀ hypothesis is used by applying it to a value
example (P : ℕ → Prop) (h : ∀ n, P n) : P 5 := h 5
-- BOOK: end quant-forall

-- BOOK: begin quant-exists
-- To show an ∃, offer a witness with use
example : ∃ n : ℕ, 3 < n := by
  use 4
  norm_num

-- from an ∃ hypothesis, extract the witness with obtain
example (P : ℕ → Prop) (h : ∃ n, P n) : ∃ m, P m := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, hn⟩
-- BOOK: end quant-exists

-- BOOK: begin quant-order
-- ∀ n, ∃ m, n < m is true: the witness may depend on n
example : ∀ n : ℕ, ∃ m : ℕ, n < m := by
  intro n
  exact ⟨n + 1, Nat.lt_succ_self n⟩

-- ∃ m, ∀ n, n < m is false: one m cannot serve every n
example : ¬ ∃ m : ℕ, ∀ n : ℕ, n < m := by
  rintro ⟨m, hm⟩
  exact absurd (hm m) (lt_irrefl m)
-- BOOK: end quant-order

-- BOOK: begin quant-example
-- The product of two consecutive integers is even
example (n : ℤ) : 2 ∣ n * (n + 1) := by
  rcases Int.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact ⟨k * (n + 1), by rw [hk]; ring⟩
  · exact ⟨n * (k + 1), by rw [hk]; ring⟩
-- BOOK: end quant-example

end Handbook.C05
