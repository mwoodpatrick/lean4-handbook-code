/- 第5章 証明の基本
   5.2 含意は関数である -/
import Mathlib

namespace Handbook.C05

-- BOOK: begin imp-fun
-- 含意 P → Q の証明は「P の証明から Q の証明を作る関数」
example (P : Prop) : P → P :=
  fun hp => hp

-- 三段論法は関数合成にすぎない
example (P Q R : Prop) (h1 : P → Q) (h2 : Q → R) : P → R :=
  fun hp => h2 (h1 hp)
-- BOOK: end imp-fun

-- BOOK: begin imp-contrapose
-- 対偶: P → Q から ¬Q → ¬P が出る(mt = modus tollens)
example (P Q : Prop) (h : P → Q) : ¬Q → ¬P :=
  mt h

-- タクティクなら contrapose! で「対偶を示す」に切り替える。
-- 「n² が偶数なら n も偶数」を「n が奇数なら n² も奇数」で示す。
example (n : ℕ) (h : n ^ 2 % 2 = 0) : n % 2 = 0 := by
  contrapose! h
  have h1 : n % 2 = 1 := by omega
  rw [Nat.pow_mod, h1]
  norm_num
-- BOOK: end imp-contrapose

-- BOOK: begin imp-curry
-- 仮定が2つあるとき「かつ」で束ねても矢印を2本並べても同値
example (P Q R : Prop) : (P ∧ Q → R) ↔ (P → Q → R) := by
  constructor
  · intro h hp hq
    exact h ⟨hp, hq⟩
  · rintro h ⟨hp, hq⟩
    exact h hp hq

-- 矢印は右結合。P → Q → R は P → (Q → R) の意味である
example (P Q R : Prop) (h : P → Q → R) (hp : P) : Q → R := h hp
-- BOOK: end imp-curry

end Handbook.C05
