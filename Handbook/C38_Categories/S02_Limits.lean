/- 第38章 圏論
   38.3 普遍性と極限・余極限 -/
import Mathlib

namespace Handbook.C38

open CategoryTheory Limits

-- BOOK: begin terminal
-- 終対象: どの対象からもただ1本の射が来る対象
#check @CategoryTheory.Limits.HasTerminal

-- 型の圏では単元型 PUnit が終対象にあたる
example (X : Type) (f g : X → PUnit) : f = g := by
  funext x
  exact Subsingleton.elim _ _
-- BOOK: end terminal

-- BOOK: begin product
-- 積の普遍性: 2本の射から積への射がただ1つ定まる
#check @CategoryTheory.Limits.HasBinaryProduct

-- 型の圏では直積が積。射影と対で普遍性を満たす
example (X Y Z : Type) (f : Z → X) (g : Z → Y) :
    ∃! h : Z → X × Y, (fun z => (h z).1) = f
      ∧ (fun z => (h z).2) = g := by
  refine ⟨fun z => (f z, g z), ⟨rfl, rfl⟩, ?_⟩
  rintro h ⟨rfl, rfl⟩
  rfl
-- BOOK: end product

-- BOOK: begin limit
-- 極限: 図式に対する「最良の錐」。積・等化子・引き戻しの統一
#check @CategoryTheory.Limits.HasLimit

-- 余極限はその双対(矢印をすべて逆にする)
#check @CategoryTheory.Limits.HasColimit
-- BOOK: end limit

end Handbook.C38
