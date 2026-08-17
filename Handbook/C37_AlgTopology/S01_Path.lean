/- 第37章 代数的トポロジー
   37.1 ホモトピーと道 -/
import Mathlib

namespace Handbook.C37

-- BOOK: begin path-basic
-- 道: 単位区間から空間への連続写像。始点と終点を型で持つ
#check @Path

-- 定値の道(その場にとどまる)
example (X : Type) [TopologicalSpace X] (x : X) : Path x x :=
  Path.refl x

-- 道は逆向きにたどれる
example (X : Type) [TopologicalSpace X] (x y : X) (p : Path x y) :
    Path y x :=
  p.symm
-- BOOK: end path-basic

-- BOOK: begin path-trans
-- 道はつなげられる。x→y と y→z をつないで x→z
noncomputable example (X : Type) [TopologicalSpace X] (x y z : X)
    (p : Path x y) (q : Path y z) : Path x z :=
  p.trans q

-- 道は連続写像で送れる
example (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x y : X) (p : Path x y) : Path (f x) (f y) :=
  p.map f.continuous
-- BOOK: end path-trans

-- BOOK: begin homotopy
-- ホモトピー: 2つの道を連続的に変形しあえる関係
#check @Path.Homotopy

-- ホモトピック(変形しあえる)は同値関係である
example (X : Type) [TopologicalSpace X] (x y : X) :
    Equivalence (@Path.Homotopic X _ x y) :=
  Path.Homotopic.equivalence
-- BOOK: end homotopy

end Handbook.C37
