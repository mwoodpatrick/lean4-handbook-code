/- 第41章 証明自動化
   41.6 自動化の境界 -/
import Mathlib

namespace Handbook.C41

-- BOOK: begin limit-omega
-- omega は整数の線形式なら決定できる
example (n m : ℕ) (h : 2 * n + 3 * m = 12) (h2 : m = 2) : n = 3 := by
  omega

-- 積が入ると線形でなくなり、omega の範囲を出る。
-- nlinarith に補助項を渡して閉じる
example (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ x * y := by
  positivity
-- BOOK: end limit-omega

-- BOOK: begin limit-ring
-- ring は可換環の等式なら閉じる。不等式は扱えない
example (a b : ℤ) : (a - b) * (a + b) = a ^ 2 - b ^ 2 := by ring

-- 不等式は linarith の領分。等式と不等式で道具が違う
example (a b : ℝ) (h : a ≤ b) : a - b ≤ 0 := by linarith
-- BOOK: end limit-ring

-- BOOK: begin limit-decide
-- decide は有限で決定可能なら閉じる
example : ∀ n : Fin 4, n.val < 4 := by decide

-- 無限の全称は decide では閉じない。帰納法か既存補題を使う
example : ∀ n : ℕ, 0 ≤ n := fun n => Nat.zero_le n
-- BOOK: end limit-decide

-- BOOK: begin limit-simp
-- simp は書き換えの繰り返し。方向が定まる規則にしか使えない
example (l : List ℕ) : (l ++ []).length = l.length := by simp

-- 可換律のような「向きのない」等式は ring/abel の担当
example (a b : ℤ) : a + b = b + a := by ring
-- BOOK: end limit-simp

end Handbook.C41
