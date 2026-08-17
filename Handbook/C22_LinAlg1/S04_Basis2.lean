/- 第22章 線形代数I
   22.3 線形独立と基底(続き) -/
import Mathlib

namespace Handbook.C22

-- BOOK: begin indep-def
-- 線形独立: 零ベクトルを作る一次結合は自明なものだけ
#check @LinearIndependent

-- 基底は線形独立である(定義の一部)
#check @Module.Basis.linearIndependent
-- BOOK: end indep-def

-- BOOK: begin basis-repr
-- 基底があれば座標が定まる。repr が「係数を読み取る」同型
#check @Module.Basis.repr

-- 次元は基底の濃度に等しい
#check @Module.finrank_eq_card_basis
-- BOOK: end basis-repr

-- BOOK: begin basis-exists
-- どんなベクトル空間にも基底がある(選択公理を使う、第28章)
example (K V : Type) [Field K] [AddCommGroup V] [Module K V] :
    ∃ s : Set V, Nonempty (Module.Basis s K V) :=
  Module.Basis.exists_basis K V
-- BOOK: end basis-exists

-- BOOK: begin span-singleton
-- 1つのベクトルが張る部分空間は「その定数倍全体」
example (K V : Type) [Field K] [AddCommGroup V] [Module K V]
    (v w : V) :
    w ∈ Submodule.span K {v} ↔ ∃ c : K, c • v = w :=
  Submodule.mem_span_singleton
-- BOOK: end span-singleton

end Handbook.C22
