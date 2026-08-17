/- 第42章 メタプログラミングと tactic 開発
   42.3 Expr と MetaM — 項の内部表現 -/
import Mathlib

namespace Handbook.C42

open Lean Meta

-- BOOK: begin expr-inspect
-- 項の内部表現(Expr)を MetaM の中で組み立てて表示する
#eval show MetaM Unit from do
  let e ← mkAppM ``Nat.add #[mkNatLit 1, mkNatLit 2]
  IO.println (← ppExpr e)  -- 出力: 1 + 2
-- BOOK: end expr-inspect

-- BOOK: begin expr-kind
-- Expr は木構造。どの構成子かを見て分岐する
#eval show MetaM Unit from do
  let e ← mkAppM ``Nat.succ #[mkNatLit 0]
  match e with
  | .app f a =>
      IO.println s!"app: 関数={← ppExpr f}, 引数={← ppExpr a}"
  | .const n _ => IO.println s!"const: {n}"
  | _ => IO.println "その他"
-- BOOK: end expr-kind

-- BOOK: begin expr-whnf
-- whnf は弱頭正規形へ簡約する。項を「計算」できる
#eval show MetaM Unit from do
  let e ← mkAppM ``Nat.add #[mkNatLit 2, mkNatLit 3]
  IO.println (← ppExpr e)      -- 出力: 2 + 3
  let v ← whnf e               -- 簡約する
  IO.println (← ppExpr v)      -- 出力: 5
-- BOOK: end expr-whnf

end Handbook.C42
