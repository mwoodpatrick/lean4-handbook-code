/- 付録A tactic リファレンス
   算術と自動化の tactic -/
import Mathlib

namespace Handbook.AppA

-- BOOK: begin t-ring
-- ring: 可換環の等式を正規形に直して閉じる
example (a b : ℤ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  ring
-- BOOK: end t-ring

-- BOOK: begin t-linarith
-- linarith: 線形の不等式。仮定を線形結合して矛盾を作る
example (x y : ℝ) (h1 : x ≤ 3) (h2 : y ≤ 2) : x + y ≤ 5 := by
  linarith
-- BOOK: end t-linarith

-- BOOK: begin t-nlinarith
-- nlinarith: 非線形。平方の非負性などを自分で足して使う
example (x : ℝ) : 0 ≤ x ^ 2 + 2 * x + 1 := by
  nlinarith [sq_nonneg (x + 1)]
-- BOOK: end t-nlinarith

-- BOOK: begin t-norm-num
-- norm_num: 数値の計算・比較・素数判定
example : (2 : ℝ) + 2 = 4 := by norm_num

example : Nat.Prime 101 := by norm_num
-- BOOK: end t-norm-num

-- BOOK: begin t-omega
-- omega: ℕ と ℤ の線形算術。減算や剰余も扱える
example (n : ℕ) (h : n > 3) : n - 1 > 2 := by omega

example (a b : ℤ) (h : 2 * a + 3 * b = 7) (h2 : a = 2) : b = 1 := by
  omega
-- BOOK: end t-omega

-- BOOK: begin t-positivity
-- positivity: 正・非負・非ゼロを構文から判定する
example (x : ℝ) (hx : 0 < x) : 0 < x ^ 2 + x := by positivity

example (x : ℝ) : 0 ≤ x ^ 2 + 1 := by positivity
-- BOOK: end t-positivity

-- BOOK: begin t-field-simp
-- field_simp: 分母を払う。分母が 0 でないことが要る
example (x : ℝ) (hx : x ≠ 0) : 1 / x + 1 = (1 + x) / x := by
  field_simp
-- BOOK: end t-field-simp

-- BOOK: begin t-linear-combination
-- linear_combination: 仮定の線形結合でゴールの等式を作る
example (x y : ℝ) (h1 : x + y = 3) (h2 : x - y = 1) : x = 2 := by
  linear_combination (h1 + h2) / 2
-- BOOK: end t-linear-combination

-- BOOK: begin t-gcongr
-- gcongr: 不等式の対応する部分だけを比べる
example (a b c : ℝ) (h : a ≤ b) (hc : 0 ≤ c) : c * a ≤ c * b := by
  gcongr
-- BOOK: end t-gcongr

-- BOOK: begin t-decide
-- decide: 決定可能な命題を全数検査で閉じる
example : (7 : ℕ) ∣ 91 := by decide

example : ∀ n : Fin 5, n.val < 5 := by decide
-- BOOK: end t-decide

-- BOOK: begin t-simp
-- simp: 単純化規則を繰り返し当てる。only で規則を限定
example (l : List ℕ) : (l ++ []).length = l.length := by simp

example (a : ℕ) : a + 0 = a := by simp only [Nat.add_zero]
-- BOOK: end t-simp

-- BOOK: begin t-cast
-- push_cast / exact_mod_cast: 型強制(↑)を動かして揃える
example (n : ℕ) : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by
  push_cast
  ring

example (n : ℕ) (h : (n : ℤ) = 3) : n = 3 := by
  exact_mod_cast h
-- BOOK: end t-cast

end Handbook.AppA
