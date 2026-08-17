/- 第5章 証明の基本
   5.10 証明が通らないときに何を見るか -/
import Mathlib

namespace Handbook.C05

-- BOOK: begin read-show
-- show はゴールを定義的に等しい形へ言い換える。
-- ¬P の正体が P → False であることを画面に出せる。
example (P : Prop) (h : P → False) : ¬P := by
  show P → False
  exact h
-- BOOK: end read-show

-- BOOK: begin read-apply
-- apply は結論を合わせに行く。合わないときは
-- 「どの引数が残ったか」を見ると原因が分かる。
example (a b c : ℕ) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  apply le_trans h1   -- 残ったゴールは b ≤ c
  exact h2
-- BOOK: end read-apply

-- BOOK: begin read-cast
-- exact は型が厳密に一致するときだけ通る。
-- ℕ と ℤ が混ざったら push_cast で型をそろえる。
example (n : ℕ) (h : 2 ≤ n) : (2 : ℤ) ≤ (n : ℤ) := by
  exact_mod_cast h
-- BOOK: end read-cast

-- BOOK: begin read-rw-fail
-- rw は「構文として一致する部分」しか書き換えない。
-- 束縛変数の下には届かないので、simp only を使う。
example (f : ℕ → ℕ) (h : ∀ x, f x = x) :
    (fun y => f y) = fun y => y := by
  simp only [h]
-- BOOK: end read-rw-fail

-- BOOK: begin read-eps
-- 解析への予告。どんな正の数以下でもあるなら 0 以下である。
-- 背理法 → 否定の整理 → 反例となる ε を自分で作る、の3手。
example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by
  by_contra hx
  push Not at hx        -- hx : 0 < x
  have h2 := h (x / 2) (by linarith)
  linarith
-- BOOK: end read-eps

end Handbook.C05
