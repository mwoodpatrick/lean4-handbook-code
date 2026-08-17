/- 第41章 証明自動化
   41.2 simp の内部動作と simp set 設計 -/
import Mathlib

namespace Handbook.C41

-- BOOK: begin simp-basic
-- simp は登録された等式を左から右へ書き換え続ける
example (a : ℕ) : a + 0 = a := by simp
example (l : List ℕ) : (l ++ []).length = l.length := by simp

-- simp? は使った補題を表示する。何が効いたか分かる
example (a : ℕ) : a * 1 + 0 = a := by simp
-- BOOK: end simp-basic

-- BOOK: begin simp-only
-- simp only は指定した補題だけを使う。暴走を防げる
example (a b : ℕ) : a + b + 0 = a + b := by
  simp only [Nat.add_zero]

-- simp に補題を足す / 外す
example (a : ℕ) (h : a = 5) : a + 0 = 5 := by simp [h]
-- BOOK: end simp-only

-- BOOK: begin simp-attr
-- @[simp] を付けると simp set に登録される
@[simp] theorem double_eq (n : ℕ) : 2 * n = n + n := by ring

example (n : ℕ) : 2 * n = n + n := by simp
-- BOOK: end simp-attr

-- BOOK: begin simp-loop
-- 向きが悪いと simp は止まらない。左辺より右辺が「単純」であること
-- 下は登録すると a + b → b + a → a + b と循環するので登録しない
example (a b : ℕ) : a + b = b + a := by
  rw [Nat.add_comm]
-- BOOK: end simp-loop

end Handbook.C41
