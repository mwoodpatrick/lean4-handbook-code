/- 第17章 実数と数列の極限
   17.5 極限の性質(四則・はさみうち) -/
import Mathlib

namespace Handbook.C17

open Filter Topology

-- BOOK: begin limits-add
-- 極限の和は和の極限。ドット記法 ha.add hb で合成できる。
example (a b : ℕ → ℝ) (L M : ℝ)
    (ha : Tendsto a atTop (𝓝 L))
    (hb : Tendsto b atTop (𝓝 M)) :
    Tendsto (fun n => a n + b n) atTop (𝓝 (L + M)) :=
  ha.add hb
-- BOOK: end limits-add

-- BOOK: begin limits-squeeze
-- はさみうちの原理
example (a b c : ℕ → ℝ) (L : ℝ)
    (hab : ∀ n, a n ≤ b n) (hbc : ∀ n, b n ≤ c n)
    (ha : Tendsto a atTop (𝓝 L))
    (hc : Tendsto c atTop (𝓝 L)) :
    Tendsto b atTop (𝓝 L) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le ha hc hab hbc
-- BOOK: end limits-squeeze

-- BOOK: begin limits-mul
-- 積の極限も合成で書ける
example (a b : ℕ → ℝ) (L M : ℝ)
    (ha : Tendsto a atTop (𝓝 L))
    (hb : Tendsto b atTop (𝓝 M)) :
    Tendsto (fun n => a n * b n) atTop (𝓝 (L * M)) :=
  ha.mul hb

-- 極限は一意(ℝ はハウスドルフ空間だから)
example (a : ℕ → ℝ) (L M : ℝ)
    (hL : Tendsto a atTop (𝓝 L))
    (hM : Tendsto a atTop (𝓝 M)) : L = M :=
  tendsto_nhds_unique hL hM
-- BOOK: end limits-mul

end Handbook.C17
