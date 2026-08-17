/- 第5章 証明の基本
   5.6 等式と書き換え -/
import Mathlib

namespace Handbook.C05

-- BOOK: begin rw-basic
-- rw は等式で左辺を右辺に置き換える
example (a b : ℕ) (h : a = b) : a + 3 = b + 3 := by
  rw [h]

example (a b c : ℕ) (h1 : a = b) (h2 : b = c) : a = c := by
  rw [h1, h2]
-- BOOK: end rw-basic

-- BOOK: begin rw-calc
-- calc は式変形の連鎖を紙の計算のように書く
example (a b : ℕ) (h1 : a = 2 * b) (h2 : b = 3) : a = 6 := by
  calc a = 2 * b := h1
    _ = 2 * 3 := by rw [h2]
    _ = 6 := rfl
-- BOOK: end rw-calc

-- BOOK: begin rw-at
-- rw はゴールだけでなく仮説の中も書き換えられる
example (a b : ℕ) (h1 : a = b) (h2 : a + 1 = 5) :
    b + 1 = 5 := by
  rw [h1] at h2
  exact h2

-- 逆向きに使うには ← を付ける
example (a b : ℕ) (h : a = b) : b + 3 = a + 3 := by
  rw [← h]
-- BOOK: end rw-at

-- BOOK: begin rw-calc-ineq
-- calc は等式だけでなく不等式の連鎖にも使える
example (a b : ℕ) (h : a ≤ b) : a ≤ b + 3 := by
  calc a ≤ b := h
    _ ≤ b + 3 := Nat.le_add_right b 3
-- BOOK: end rw-calc-ineq

end Handbook.C05
