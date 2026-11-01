module DASHI.Moonshine.JInvariantBishopUpperHalfPlaneQuotientRadiusWeldExact where

------------------------------------------------------------------------
-- BISHOP UPPER-HALF-PLANE RADIUS -> LEGACY QUOTIENT WELD
--
-- DASHI CONTRIBUTION
--
-- The Bishop-side analytic theorem is now concrete:
--
--   pi_B > 0, Im_B tau > 0
--     -> r_B = exp(-(2*pi_B*Im_B tau)) lies in [0,1)
--     -> the E4/E6 polynomial-geometric majorants converge absolutely.
--
-- Separately, any concrete propositional quotient of the selected Bishop
-- setoid backend induces the canonical cross-carrier radius relation
--
--   quotient(r_B) = r_legacy.
--
-- This owner composes those two already-owned pieces.  It does NOT identify
-- quotient(r_B) with the older ConcreteComplex literal |q(tau)|, and it does
-- NOT identify pi_B with the legacy/trigonometric pi.  Those same-object
-- statements remain explicit downstream obligations.
------------------------------------------------------------------------

import Real as BishopReal

import DASHI.Analysis.ConstructedRealBackendSpineExact as Spine
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneRadiusExact as Radius
import DASHI.Moonshine.JInvariantEisensteinBishopRadiusWeldExact as Weld

upperHalfPlaneRadiusWeldFromConcreteBishopQuotient :
  (Q : Spine.PropositionalQuotientRealization Weld.BishopSetoidReal) →
  ∀ {piB imag : BishopReal.ℝ} →
  BishopReal._<_ BishopReal.0ℝ piB →
  BishopReal._<_ BishopReal.0ℝ imag →
  Weld.LiteralRadiusBishopWeld
    (Weld.QuotientRadiusRelation Q)
    (Spine.quotient Q (Radius.qRadius piB imag))
upperHalfPlaneRadiusWeldFromConcreteBishopQuotient Q {piB} {imag} piPositive imagPositive =
  Weld.radiusWeldFromConcreteBishopQuotient
    Q
    (Radius.qRadius piB imag)
    (Radius.qRadiusUnitInterval piPositive imagPositive)

upperHalfPlaneMajorantsFromConcreteBishopQuotient :
  (Q : Spine.PropositionalQuotientRealization Weld.BishopSetoidReal) →
  ∀ {piB imag : BishopReal.ℝ} →
  (piPositive : BishopReal._<_ BishopReal.0ℝ piB) →
  (imagPositive : BishopReal._<_ BishopReal.0ℝ imag) →
  Weld.EisensteinBishopMajorantReceipt
    (Weld.QuotientRadiusRelation Q)
    (Spine.quotient Q (Radius.qRadius piB imag))
    (upperHalfPlaneRadiusWeldFromConcreteBishopQuotient
      Q piPositive imagPositive)
upperHalfPlaneMajorantsFromConcreteBishopQuotient
  Q piPositive imagPositive =
  Weld.compileEisensteinBishopMajorants
    (upperHalfPlaneRadiusWeldFromConcreteBishopQuotient
      Q piPositive imagPositive)
