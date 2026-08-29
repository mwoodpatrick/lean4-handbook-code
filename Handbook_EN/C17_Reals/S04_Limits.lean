/- Chapter 17: Real numbers and limits of sequences
   17.5 Properties of limits -/
import Mathlib

open Filter Topology

namespace Handbook.C17

-- BOOK: begin limits-add
-- The limit of a sum is the sum of the limits;
-- dot notation ha.add hb composes them
example (a b : ℕ → ℝ) (L M : ℝ)
    (ha : Tendsto a atTop (𝓝 L))
    (hb : Tendsto b atTop (𝓝 M)) :
    Tendsto (fun n => a n + b n) atTop (𝓝 (L + M)) :=
  ha.add hb
-- BOOK: end limits-add

-- BOOK: begin limits-mul-unique
-- The limit of a product is written by composition too
example (a b : ℕ → ℝ) (L M : ℝ)
    (ha : Tendsto a atTop (𝓝 L))
    (hb : Tendsto b atTop (𝓝 M)) :
    Tendsto (fun n => a n * b n) atTop (𝓝 (L * M)) :=
  ha.mul hb

-- The limit is unique (because ℝ is a Hausdorff space)
example (a : ℕ → ℝ) (L M : ℝ)
    (hL : Tendsto a atTop (𝓝 L))
    (hM : Tendsto a atTop (𝓝 M)) : L = M :=
  tendsto_nhds_unique hL hM
-- BOOK: end limits-mul-unique

-- BOOK: begin limits-squeeze
-- The squeeze theorem
example (a b c : ℕ → ℝ) (L : ℝ)
    (hab : ∀ n, a n ≤ b n) (hbc : ∀ n, b n ≤ c n)
    (ha : Tendsto a atTop (𝓝 L))
    (hc : Tendsto c atTop (𝓝 L)) :
    Tendsto b atTop (𝓝 L) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le ha hc hab hbc
-- BOOK: end limits-squeeze

end Handbook.C17
