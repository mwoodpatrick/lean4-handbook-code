/- 第40章 mathlib の歩き方
   40.5 型クラス階層の泳ぎ方 -/
import Mathlib

namespace Handbook.C40

-- BOOK: begin synth
-- #synth は「そのインスタンスをどう見つけたか」を答える
#synth AddCommMonoid ℕ
#synth Ring ℤ
#synth Field ℚ
#synth TopologicalSpace ℝ
-- BOOK: end synth

-- BOOK: begin synth-chain
-- 階層は上へ遡れる。体は環でもある
example : Ring ℚ := by infer_instance
example : CommRing ℚ := by infer_instance
example : AddCommGroup ℚ := by infer_instance

-- ℕ には減法がないので Ring にはならない(下の行はエラーになる)
-- example : Ring ℕ := by infer_instance
-- BOOK: end synth-chain

-- BOOK: begin synth-use
-- 一般の型クラス仮定で書けば、当てはまる型すべてで使える
example (R : Type) [CommRing R] (a b : R) :
    (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  ring

-- ℤ でも ℚ でも多項式環でも、同じ定理が通る
example (a b : ℤ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  ring
-- BOOK: end synth-use

end Handbook.C40
