/- English edition source: Handbook/C24_Multivar/S01_FDeriv.lean. -/
import Mathlib

namespace Handbook.C24

-- BOOK: begin fderiv
-- The total derivative is the best approximation by a continuous
-- linear map
#check @fderiv

-- The total derivative of the map taking the first component is the
-- linear map taking the first component itself
example (p : ℝ × ℝ) :
    HasFDerivAt Prod.fst (ContinuousLinearMap.fst ℝ ℝ ℝ) p :=
  hasFDerivAt_fst
-- BOOK: end fderiv

-- BOOK: begin fderiv-defn
-- The definition itself: f(x+h) − f(x) − f'(h) goes to 0 faster
-- than ‖h‖
#check @hasFDerivAt_iff_isLittleO

-- The same condition written as a limit of a quotient (as in the
-- one-variable definition)
#check @hasFDerivAt_iff_tendsto
-- BOOK: end fderiv-defn

-- BOOK: begin fderiv-basic
-- The total derivative of a constant map is 0 (no change in any
-- direction)
example (c : ℝ) (x : ℝ × ℝ) :
    HasFDerivAt (fun _ : ℝ × ℝ => c) (0 : ℝ × ℝ →L[ℝ] ℝ) x :=
  hasFDerivAt_const c x

-- The total derivative of the identity is the identity linear map
example (x : ℝ × ℝ) :
    HasFDerivAt id (ContinuousLinearMap.id ℝ (ℝ × ℝ)) x :=
  hasFDerivAt_id x
-- BOOK: end fderiv-basic

-- BOOK: begin fderiv-bridge
-- The one-variable HasDerivAt is a special case of HasFDerivAt
-- (the linear map multiplying by c)
example (f : ℝ → ℝ) (c x : ℝ) :
    HasDerivAt f c x ↔
      HasFDerivAt f (ContinuousLinearMap.toSpanSingleton ℝ c) x :=
  hasDerivAt_iff_hasFDerivAt
-- BOOK: end fderiv-bridge

-- BOOK: begin fderiv-chain
-- The chain rule: derivatives of a composition compose
example (f : ℝ × ℝ → ℝ) (g : ℝ → ℝ × ℝ) (x : ℝ)
    (f' : ℝ × ℝ →L[ℝ] ℝ) (g' : ℝ →L[ℝ] ℝ × ℝ)
    (hf : HasFDerivAt f f' (g x)) (hg : HasFDerivAt g g' x) :
    HasFDerivAt (f ∘ g) (f'.comp g') x :=
  hf.comp x hg
-- BOOK: end fderiv-chain

end Handbook.C24
