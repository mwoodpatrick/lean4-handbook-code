/- English edition source: Handbook/C42_Meta/S02_Expr.lean. -/
import Mathlib

namespace Handbook.C42

open Lean Meta

-- BOOK: begin expr-inspect
-- Build and display the internal representation (Expr) of a term
-- inside MetaM
#eval show MetaM Unit from do
  let e ← mkAppM ``Nat.add #[mkNatLit 1, mkNatLit 2]
  IO.println (← ppExpr e)  -- Output: 1 + 2
-- BOOK: end expr-inspect

-- BOOK: begin expr-kind
-- An Expr is a tree; we inspect which constructor it is
#eval show MetaM Unit from do
  let e ← mkAppM ``Nat.succ #[mkNatLit 0]
  match e with
  | .app f a =>
      IO.println s!"app: f={← ppExpr f}, a={← ppExpr a}"
  | .const n _ => IO.println s!"const: {n}"
  | _ => IO.println "Others"
-- BOOK: end expr-kind

-- BOOK: begin expr-whnf
-- whnf reduces to weak head normal form, computing just enough
#eval show MetaM Unit from do
  let e ← mkAppM ``Nat.add #[mkNatLit 2, mkNatLit 3]
  IO.println (← ppExpr e)      -- Output: 2 + 3
  let v ← whnf e               -- Close
  IO.println (← ppExpr v)      -- Output: 5
-- BOOK: end expr-whnf

end Handbook.C42
