/- 付録A tactic リファレンス
   構造を扱う tactic と分野別の自動化 -/
import Mathlib

namespace Handbook.AppA

-- BOOK: begin t-induction
-- induction: 帰納法。with で各場合に名前を付ける
example (n : ℕ) : 0 ≤ n := by
  induction n with
  | zero => exact le_refl 0
  | succ k ih => exact Nat.le_succ_of_le ih
-- BOOK: end t-induction

-- BOOK: begin t-by-cases
-- by_cases: 命題の真偽で場合分け(排中律を使う)
example (p : Prop) [Decidable p] (q : Prop) (hq : q) :
    (p → q) ∧ (¬p → q) := by
  constructor
  · intro _; exact hq
  · intro _; exact hq

example (x : ℝ) : x ≤ |x| := by
  by_cases h : 0 ≤ x
  · rw [abs_of_nonneg h]
  · push Not at h
    rw [abs_of_neg h]
    linarith
-- BOOK: end t-by-cases

-- BOOK: begin t-ext
-- ext: 相等を「各点で等しい」に還元する
example (f g : ℕ → ℕ) (h : ∀ n, f n = g n) : f = g := by
  ext n
  exact h n

example (s t : Set ℕ) (h : ∀ x, x ∈ s ↔ x ∈ t) : s = t := by
  ext x
  exact h x
-- BOOK: end t-ext

-- BOOK: begin t-funext
-- funext: 関数の相等の専用版
example (f : ℕ → ℕ) : (fun n => f n) = f := by
  funext n
  rfl
-- BOOK: end t-funext

-- BOOK: begin t-push-neg
-- push Not: 否定を内側へ押し込む。¬∀ を ∃¬ に直す。
-- 旧称 push_neg は v4.32 で非推奨(動くが警告が出る)
example (f : ℕ → ℕ) (h : ¬ ∀ n, f n = 0) : ∃ n, f n ≠ 0 := by
  push Not at h
  exact h
-- BOOK: end t-push-neg

-- BOOK: begin t-specialize
-- specialize: 全称の仮定に具体的な値を入れて特殊化する
example (f : ℕ → ℕ) (h : ∀ n, f n = n) : f 3 = 3 := by
  specialize h 3
  exact h
-- BOOK: end t-specialize

-- BOOK: begin t-have
-- have / show: 補助命題を立てる / ゴールを別の形で書き直す
example (a b : ℝ) (h : a = b) : a + 1 = b + 1 := by
  have h2 : a + 1 = b + 1 := by rw [h]
  show a + 1 = b + 1
  exact h2
-- BOOK: end t-have

-- BOOK: begin t-set
-- set: 式に名前を付け、ゴール中の出現をまとめて置き換える
example (x y : ℝ) (h : x + y = 3) : (x + y) ^ 2 = 9 := by
  set s := x + y with hs
  rw [h]
  norm_num
-- BOOK: end t-set

-- BOOK: begin t-group
-- group / abel: 群・可換群の等式を公理から閉じる
example (G : Type) [Group G] (a b : G) :
    a * b * b⁻¹ = a := by group

example (A : Type) [AddCommGroup A] (a b : A) :
    a + b - b = a := by abel
-- BOOK: end t-group

-- BOOK: begin t-funprop
-- fun_prop: 連続性・可測性・可微分性を構文から組み立てる
example : Continuous (fun x : ℝ => x ^ 2 + Real.sin x) := by
  fun_prop

example : Differentiable ℝ (fun x : ℝ => Real.exp x * x) := by
  fun_prop
-- BOOK: end t-funprop

-- BOOK: begin t-aesop
-- aesop: ルールベースの証明探索。論理と集合の雑務に強い
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by aesop

example (s t : Set ℕ) (x : ℕ) (h : x ∈ s) : x ∈ s ∪ t := by
  aesop
-- BOOK: end t-aesop

-- BOOK: begin t-search
-- exact? はゴールを閉じる補題をライブラリから探す。
-- 見つかった補題名で置き換えて使う(下は探索結果の形)
example (a b : ℕ) (h : a ≤ b) : a ≤ b + 1 :=
  le_add_right h
-- BOOK: end t-search

end Handbook.AppA
