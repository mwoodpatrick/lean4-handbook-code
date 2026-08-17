/- 付録A tactic リファレンス
   基本の tactic(項を当てる・仮定を動かす・書き換える) -/
import Mathlib

namespace Handbook.AppA

-- BOOK: begin t-exact
-- exact: ゴールに項をぴったり当てる
example (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  ⟨hp, hq⟩

example (p : Prop) (hp : p) : p := by exact hp
-- BOOK: end t-exact

-- BOOK: begin t-apply
-- apply: ゴールを補題の前提へ後退させる
example (p q : Prop) (h : p → q) (hp : p) : q := by
  apply h
  exact hp
-- BOOK: end t-apply

-- BOOK: begin t-intro
-- intro: 含意の前件・全称の変数を仮定に取り込む
example (p q : Prop) : p → q → p := by
  intro hp _
  exact hp

example (f : ℕ → ℕ) (h : ∀ n, f n = n) : ∀ n, f n = n := by
  intro n
  exact h n
-- BOOK: end t-intro

-- BOOK: begin t-rfl
-- rfl: 定義上等しいものを閉じる。計算は簡約で進む
example : 2 + 2 = 4 := rfl

example (l : List ℕ) : l ++ [] = l := by simp
-- BOOK: end t-rfl

-- BOOK: begin t-rw
-- rw: 等式で書き換える。← で右から左へ
example (a b c : ℕ) (h : a = b) : a + c = b + c := by
  rw [h]

example (a b : ℕ) (h : a = b) : b = a := by
  rw [← h]
-- BOOK: end t-rw

-- BOOK: begin t-use
-- use: 存在量化に証拠を与える
example : ∃ n : ℕ, n * n = 49 := by
  use 7
-- BOOK: end t-use

-- BOOK: begin t-obtain
-- obtain: 構造を分解して取り出す(∃ や ∧ を開く)
example (p q : Prop) (h : p ∧ q) : q := by
  obtain ⟨_, hq⟩ := h
  exact hq

example (f : ℕ → ℕ) (h : ∃ n, f n = 0) : True := by
  obtain ⟨n, hn⟩ := h
  trivial
-- BOOK: end t-obtain

-- BOOK: begin t-rintro
-- rintro: intro と分解を一手で行う
example (p q : Prop) : p ∧ q → q := by
  rintro ⟨_, hq⟩
  exact hq
-- BOOK: end t-rintro

-- BOOK: begin t-constructor
-- constructor: 構成子を当てる(∧ を2つのゴールに割る)
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  · exact hp
  · exact hq
-- BOOK: end t-constructor

-- BOOK: begin t-refine
-- refine: 証拠を部分的に与え、残りを ?_ で穴にする
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  refine ⟨hp, ?_⟩
  exact hq
-- BOOK: end t-refine

-- BOOK: begin t-rcases
-- rcases: パターンで場合分けする(∨ を分ける)
example (p q : Prop) (h : p ∨ q) : q ∨ p := by
  rcases h with hp | hq
  · exact Or.inr hp
  · exact Or.inl hq
-- BOOK: end t-rcases

-- BOOK: begin t-calc
-- calc: 等式・不等式を段階的につなぐ
example (a b : ℕ) (h1 : a = b) (h2 : b ≤ 5) : a ≤ 5 :=
  calc a = b := h1
    _ ≤ 5 := h2
-- BOOK: end t-calc

end Handbook.AppA
