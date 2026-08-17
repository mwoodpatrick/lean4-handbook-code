/- 第12章 数列と数学的帰納法
   12.2 等差・等比数列と一般項 -/
import Mathlib

namespace Handbook.C12

-- BOOK: begin arith-def
-- 初項 a、公差 d の等差数列を漸化式で定義する
def arith (a d : ℚ) : ℕ → ℚ
  | 0 => a
  | n + 1 => arith a d n + d
-- BOOK: end arith-def

-- BOOK: begin arith-closed
-- 一般項 aₙ = a + n d。漸化式による定義と閉じた式を帰納法が結ぶ。
theorem arith_eq (a d : ℚ) (n : ℕ) :
    arith a d n = a + n * d := by
  induction n with
  | zero => simp [arith]
  | succ n ih =>
    simp only [arith, ih]
    push_cast
    ring
-- BOOK: end arith-closed

-- BOOK: begin geom-def
-- 等比数列も同じ型で書ける
def geom (a r : ℚ) : ℕ → ℚ
  | 0 => a
  | n + 1 => geom a r n * r

theorem geom_eq (a r : ℚ) (n : ℕ) :
    geom a r n = a * r ^ n := by
  induction n with
  | zero => simp [geom]
  | succ n ih =>
    simp only [geom, ih]
    ring
-- BOOK: end geom-def

end Handbook.C12
