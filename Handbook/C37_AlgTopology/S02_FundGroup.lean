/- 第37章 代数的トポロジー
   37.2 基本群 -/
import Mathlib

namespace Handbook.C37

-- BOOK: begin fundamental-group
-- 基本群: 基点付きループのホモトピー類のなす群
#check @FundamentalGroup

-- 群であることは型クラスとして与えられている
noncomputable example (X : Type) [TopologicalSpace X] (x : X) :
    Group (FundamentalGroup X x) := by
  infer_instance
-- BOOK: end fundamental-group

-- BOOK: begin fundamental-groupoid
-- 基点を固定しない版が基本亜群。基点付きはその自己射のなす群
#check @FundamentalGroupoid

-- 単連結: 道連結かつ基本群が自明
#check @SimplyConnectedSpace

-- ℝ は道連結である
example : PathConnectedSpace ℝ := by infer_instance
-- BOOK: end fundamental-groupoid

end Handbook.C37
