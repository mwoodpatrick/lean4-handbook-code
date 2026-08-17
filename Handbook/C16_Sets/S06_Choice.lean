/- 第16章 集合と写像 — 数学の言語
   16.7 選択公理との最初の遭遇 -/
import Mathlib

namespace Handbook.C16

-- BOOK: begin choice
-- Classical.choice: 「存在する」から「値そのもの」を取り出す公理
#check @Classical.choice  -- Nonempty α → α

-- 計算はできないので noncomputable の印が付く
noncomputable def pick (α : Type) (h : Nonempty α) : α :=
  Classical.choice h
-- BOOK: end choice

end Handbook.C16
