/- 第5章 証明の基本
   5.5 全称と存在 -/
import Mathlib

namespace Handbook.C05

-- BOOK: begin quant-forall
-- 全称 ∀ は intro で「任意の n を取る」
example : ∀ n : ℕ, n ≤ n + 1 := by
  intro n
  exact Nat.le_succ n
-- BOOK: end quant-forall

-- BOOK: begin quant-exists
-- 存在 ∃ は use で証拠を差し出す
example : ∃ n : ℕ, n * n = 49 := by
  use 7

-- 存在の仮定は obtain で証拠を取り出す
example (a : ℕ) (h : ∃ n, a = 2 * n) :
    ∃ m, 3 * a = 2 * m := by
  obtain ⟨n, hn⟩ := h
  use 3 * n
  omega
-- BOOK: end quant-exists

-- BOOK: begin quant-order
-- ∀∃(どの n にも上がある)は真、∃∀(全員の上が1つ)は偽
example : ∀ n : ℕ, ∃ m : ℕ, n < m :=
  fun n => ⟨n + 1, Nat.lt_succ_self n⟩

example : ¬ ∃ m : ℕ, ∀ n : ℕ, n < m := by
  rintro ⟨m, hm⟩
  exact lt_irrefl m (hm m)
-- BOOK: end quant-order

-- BOOK: begin quant-example
-- 例題: 連続する2整数の積は偶数である
example (n : ℤ) : 2 ∣ n * (n + 1) := by
  rcases Int.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact ⟨k * (n + 1), by rw [hk]; ring⟩
  · exact ⟨n * (k + 1), by rw [hk]; ring⟩
-- BOOK: end quant-example

end Handbook.C05
