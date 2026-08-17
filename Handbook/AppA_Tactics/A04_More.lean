/- 付録A tactic リファレンス
   場合分け・否定・書き換えの補助 tactic -/
import Mathlib

namespace Handbook.AppA

-- BOOK: begin t-by-contra
-- by_contra: 結論の否定を仮定して矛盾を導く
example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by
  by_contra hx
  push Not at hx
  have := h (x / 2) (by linarith)
  linarith
-- BOOK: end t-by-contra

-- BOOK: begin t-contrapose
-- contrapose!: 対偶を取る。! を付けると否定も整理する
example (n : ℕ) (h : n ^ 2 ≠ 0) : n ≠ 0 := by
  contrapose! h
  rw [h]
  ring
-- BOOK: end t-contrapose

-- BOOK: begin t-cases
-- cases: 構成子ごとに分ける。帰納法の仮定は付かない
example (n : ℕ) : n = 0 ∨ 0 < n := by
  cases n with
  | zero => exact Or.inl rfl
  | succ k => exact Or.inr (Nat.succ_pos k)
-- BOOK: end t-cases

-- BOOK: begin t-leftright
-- left / right: 選言のどちらを示すかを選ぶ
example : 2 = 2 ∨ 2 = 3 := by
  left
  rfl
-- BOOK: end t-leftright

-- BOOK: begin t-exfalso
-- exfalso: ゴールを False に置き換える(矛盾を作りにいく)
example (h : (1 : ℕ) = 2) : 3 = 4 := by
  exfalso
  omega
-- BOOK: end t-exfalso

-- BOOK: begin t-suffices
-- suffices: 「これを示せば十分」と先に宣言する
example (a b : ℝ) (h : a = b) : a + 0 = b := by
  suffices hs : a = b by simpa using hs
  exact h
-- BOOK: end t-suffices

-- BOOK: begin t-subst
-- subst: 変数の等式で全体を置き換えて仮定を消す
example (a b : ℕ) (h : a = b) : a + 1 = b + 1 := by
  subst h
  rfl
-- BOOK: end t-subst

-- BOOK: begin t-nth-rewrite
-- nth_rewrite: 何番目の出現を書き換えるかを指定する
example (a : ℕ) (h : a = 0) : a + a = a := by
  nth_rewrite 1 [h]
  rw [Nat.zero_add]
-- BOOK: end t-nth-rewrite

-- BOOK: begin t-simp-rw
-- simp_rw: 束縛変数の内側でも書き換える。
-- 下は rw [h] では通らない(λ の内側に届かないため)
example (f : ℕ → ℕ) (h : ∀ n, f n = n) :
    (fun n => f n) = (fun n => n) := by
  simp_rw [h]
-- BOOK: end t-simp-rw

-- BOOK: begin t-conv
-- conv: 書き換える位置をゴールの中で指定する。
-- conv_lhs は左辺だけを対象にする
example (a b : ℕ) (h : a = b) : a + a = b + b := by
  conv_lhs => rw [h]
-- BOOK: end t-conv

-- BOOK: begin t-splitifs
-- split_ifs: if の条件ごとにゴールを分ける
example (n : ℕ) : (if n = 0 then 0 else n) ≤ n := by
  split_ifs with h
  · exact Nat.zero_le n
  · exact le_refl n
-- BOOK: end t-splitifs

-- BOOK: begin t-interval-cases
-- interval_cases: 有界な変数を全通り列挙する
example (n : ℕ) (h1 : 2 ≤ n) (h2 : n < 5) :
    n = 2 ∨ n = 3 ∨ n = 4 := by
  interval_cases n
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
-- BOOK: end t-interval-cases

-- BOOK: begin t-tauto
-- tauto: 命題論理の恒真式を閉じる
example (p q : Prop) (h : p ∧ q) : q ∧ p := by tauto
-- BOOK: end t-tauto

-- BOOK: begin t-assumption
-- assumption / trivial: 文脈から探す / 自明なゴールを閉じる
example (p : Prop) (hp : p) : p := by assumption

example : True ∧ (2 = 2) := by
  constructor
  · trivial
  · rfl
-- BOOK: end t-assumption

end Handbook.AppA
