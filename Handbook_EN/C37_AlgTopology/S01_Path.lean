/- Chapter 37: Algebraic topology
   37.1 Homotopy and paths -/
import Mathlib

namespace Handbook.C37

-- BOOK: begin path-basic
-- A path: a continuous map out of the unit interval.
-- Its endpoints are carried in the type.
#check @Path
-- the constant path (staying put)
example (X : Type) [TopologicalSpace X] (x : X) : Path x x :=
  Path.refl x
-- a path can be traversed backwards
example (X : Type) [TopologicalSpace X] (x y : X) (p : Path x y) :
    Path y x :=
  p.symm
-- BOOK: end path-basic

-- BOOK: begin path-trans
-- Paths can be joined: x→y followed by y→z gives x→z
noncomputable example (X : Type) [TopologicalSpace X] (x y z : X)
    (p : Path x y) (q : Path y z) : Path x z :=
  p.trans q
-- a path can be pushed forward along a continuous map
example (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x y : X) (p : Path x y) : Path (f x) (f y) :=
  p.map f.continuous
-- BOOK: end path-trans

-- BOOK: begin homotopy
-- Homotopy: the relation of being continuously deformable
#check @Path.Homotopy
-- being homotopic is an equivalence relation
example (X : Type) [TopologicalSpace X] (x y : X) :
    Equivalence (@Path.Homotopic X _ x y) :=
  Path.Homotopic.equivalence
-- BOOK: end homotopy

end Handbook.C37
