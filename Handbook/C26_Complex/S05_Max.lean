/- 第26章 複素解析
   26.9 最大値原理と Liouville の定理 -/
import Mathlib

namespace Handbook.C26

-- BOOK: begin max-principle
-- 最大値原理: 連結開集合の内部で |f| が最大になったら、
-- f はその集合上で定数である
example {U : Set ℂ} {c : ℂ} {f : ℂ → ℂ}
    (hc : IsPreconnected U) (ho : IsOpen U)
    (hd : DifferentiableOn ℂ f U) (hcU : c ∈ U)
    (hm : IsMaxOn (norm ∘ f) U c) :
    Set.EqOn f (Function.const ℂ (f c)) U :=
  Complex.eqOn_of_isPreconnected_of_isMaxOn_norm hc ho hd hcU hm
-- BOOK: end max-principle

end Handbook.C26
