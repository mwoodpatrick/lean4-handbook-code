/- 第16章 集合と写像 — 数学の言語
   16.5 同値関係と商 -/
import Mathlib

namespace Handbook.C16

-- BOOK: begin setoid-def
-- 同値関係: 偶奇が同じ自然数を「同じ」とみなす
def parity : Setoid ℕ :=
  ⟨fun a b => a % 2 = b % 2,
   ⟨fun _ => rfl, Eq.symm, Eq.trans⟩⟩

-- 商型 Quotient parity は「偶奇だけを見る世界」
#check Quotient parity
-- BOOK: end setoid-def

-- BOOK: begin quotient-mk
-- 3 と 5 は商の世界では同じ元になる
example : Quotient.mk parity 3 = Quotient.mk parity 5 :=
  Quotient.sound rfl
-- BOOK: end quotient-mk

-- BOOK: begin quotient-lift
-- 商の上の関数は「代表の取り方に依らない」ことを示して定義する
-- ここでは「偶奇 → 0/1」を商から取り出す
def parityBit : Quotient parity → ℕ :=
  Quotient.lift (fun n => n % 2) (fun _ _ h => h)

example : parityBit (Quotient.mk parity 7) = 1 := rfl
-- BOOK: end quotient-lift

end Handbook.C16
