/- 第32章 位相空間論
   32.5 コンパクト性と Tychonoff の定理 -/
import Mathlib

namespace Handbook.C32

-- BOOK: begin compact-cover
-- コンパクトの定義そのもの: どの開被覆からも有限部分被覆が取れる
example (X : Type) [TopologicalSpace X] (s : Set X)
    (hs : IsCompact s) (U : ℕ → Set X) (hU : ∀ i, IsOpen (U i))
    (hsub : s ⊆ ⋃ i, U i) :
    ∃ t : Finset ℕ, s ⊆ ⋃ i ∈ t, U i :=
  hs.elim_finite_subcover U hU hsub
-- BOOK: end compact-cover

-- BOOK: begin compact-image
-- コンパクト集合の連続像はコンパクト(最大値の定理の心臓部)
example (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (s : Set X) (hs : IsCompact s)
    (hf : Continuous f) : IsCompact (f '' s) :=
  hs.image hf

-- 閉区間はコンパクト(ハイネ・ボレル。第18章の土台)
example (a b : ℝ) : IsCompact (Set.Icc a b) :=
  isCompact_Icc
-- BOOK: end compact-image

-- BOOK: begin compact-max
-- 最大値の定理: コンパクト集合上の連続関数は最大値を取る
example (s : Set ℝ) (hs : IsCompact s) (hne : s.Nonempty)
    (f : ℝ → ℝ) (hf : ContinuousOn f s) :
    ∃ x ∈ s, IsMaxOn f s x :=
  hs.exists_isMaxOn hne hf
-- BOOK: end compact-max

-- BOOK: begin tychonoff
-- Tychonoff の定理: コンパクト集合の任意個の直積はコンパクト
example (ι : Type) (X : ι → Type) [∀ i, TopologicalSpace (X i)]
    (s : ∀ i, Set (X i)) (hs : ∀ i, IsCompact (s i)) :
    IsCompact {x : ∀ i, X i | ∀ i, x i ∈ s i} :=
  isCompact_pi_infinite hs
-- BOOK: end tychonoff

-- BOOK: begin compact-fip
-- 有限交叉性: 減少する空でないコンパクト閉集合列の共通部分は空でない
example (X : Type) [TopologicalSpace X] (t : ℕ → Set X)
    (hdir : Directed (· ⊇ ·) t) (hne : ∀ i, (t i).Nonempty)
    (hcp : ∀ i, IsCompact (t i)) (hcl : ∀ i, IsClosed (t i)) :
    (⋂ i, t i).Nonempty :=
  IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    t hdir hne hcp hcl
-- BOOK: end compact-fip

end Handbook.C32
