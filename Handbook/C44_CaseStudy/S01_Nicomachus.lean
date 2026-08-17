/- 第44章 ケーススタディ — 1つの定理を形式化する
   題材: ニコマコスの定理 Σk³ = (Σk)²
   第12章の gauss_sum を補題として再利用する。 -/
import Handbook.C12_Induction.S03_Sums

namespace Handbook.C44

open Finset

-- BOOK: begin nicomachus
-- ニコマコスの定理: 1³+2³+⋯+n³ = (1+2+⋯+n)²
theorem nicomachus (n : ℕ) :
    ∑ k ∈ range (n + 1), k ^ 3
      = (∑ k ∈ range (n + 1), k) ^ 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sum_range_succ, sum_range_succ (f := fun k => (k : ℕ)),
        ih]
    set S := ∑ k ∈ range (n + 1), k with hS
    -- 鍵: 第12章のガウスの和 2S = n(n+1)
    have h2 : 2 * S = n * (n + 1) := Handbook.C12.gauss_sum n
    have key : (n + 1) ^ 3 = 2 * S * (n + 1) + (n + 1) ^ 2 := by
      rw [h2]; ring
    calc S ^ 2 + (n + 1) ^ 3
        = S ^ 2 + (2 * S * (n + 1) + (n + 1) ^ 2) := by rw [key]
      _ = (S + (n + 1)) ^ 2 := by ring
-- BOOK: end nicomachus

end Handbook.C44
