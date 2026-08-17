/- 第28章 数学基礎論と公理的集合論
   28.3 順序数と超限帰納法 -/
import Mathlib

namespace Handbook.C28

-- BOOK: begin ordinal-omega
-- 最小の無限順序数 ω。自然数全体の順序型である
#check @Ordinal.omega0

-- 順序数の加法は非可換。1 + ω は ω に飲み込まれる
example : (1 : Ordinal) + Ordinal.omega0 = Ordinal.omega0 :=
  Ordinal.one_add_omega0

-- ところが ω + 1 は ω より真に大きい
example : Ordinal.omega0 < Ordinal.omega0 + 1 := by
  rw [← Order.succ_eq_add_one]
  exact Order.lt_succ _
-- BOOK: end ordinal-omega

-- BOOK: begin ordinal-noncomm
-- 以上をまとめると 1 + ω ≠ ω + 1。
-- 「前に足す」と飲み込まれ、「後ろに足す」と伸びる
example : (1 : Ordinal) + Ordinal.omega0 ≠ Ordinal.omega0 + 1 := by
  rw [Ordinal.one_add_omega0]
  refine ne_of_lt ?_
  rw [← Order.succ_eq_add_one]
  exact Order.lt_succ _
-- BOOK: end ordinal-noncomm

-- BOOK: begin ordinal-wf
-- 順序数の < は整礎。無限降下列が作れないことが
-- 超限帰納法と超限再帰の根拠になる
#check @Ordinal.lt_wf

-- 整列可能定理: どんな型にも整列順序を入れられる(選択公理と同値)
#check @exists_wellFoundedLT
-- BOOK: end ordinal-wf

end Handbook.C28
