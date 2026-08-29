/- English edition source: Handbook/C26_Complex/S05_Max.lean. -/
import Mathlib

namespace Handbook.C26

-- BOOK: begin max-principle
-- The maximum principle: if |f| attains a maximum inside a connected
-- open set, then f is constant on that set
example {U : Set ℂ} {c : ℂ} {f : ℂ → ℂ}
    (hc : IsPreconnected U) (ho : IsOpen U)
    (hd : DifferentiableOn ℂ f U) (hcU : c ∈ U)
    (hm : IsMaxOn (norm ∘ f) U c) :
    Set.EqOn f (Function.const ℂ (f c)) U :=
  Complex.eqOn_of_isPreconnected_of_isMaxOn_norm hc ho hd hcU hm
-- BOOK: end max-principle

end Handbook.C26
