module DASHI.Moonshine.JInvariantBishopUpperHalfPlaneQuotientRadiusWeldValidation where

import Real as BishopReal

import DASHI.Analysis.ConstructedRealBackendSpineExact as Spine
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneRadiusExact as Radius
import DASHI.Moonshine.JInvariantEisensteinBishopRadiusWeldExact as Weld
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneQuotientRadiusWeldExact as P

quotientRadiusWeldRegression :
  (Q : Spine.PropositionalQuotientRealization Weld.BishopSetoidReal) →
  ∀ {piB imag : BishopReal.ℝ} →
  BishopReal._<_ BishopReal.0ℝ piB →
  BishopReal._<_ BishopReal.0ℝ imag →
  Weld.LiteralRadiusBishopWeld
    (Weld.QuotientRadiusRelation Q)
    (Spine.quotient Q (Radius.qRadius piB imag))
quotientRadiusWeldRegression =
  P.upperHalfPlaneRadiusWeldFromConcreteBishopQuotient

quotientMajorantsRegression :
  (Q : Spine.PropositionalQuotientRealization Weld.BishopSetoidReal) →
  ∀ {piB imag : BishopReal.ℝ} →
  (piPositive : BishopReal._<_ BishopReal.0ℝ piB) →
  (imagPositive : BishopReal._<_ BishopReal.0ℝ imag) →
  Weld.EisensteinBishopMajorantReceipt
    (Weld.QuotientRadiusRelation Q)
    (Spine.quotient Q (Radius.qRadius piB imag))
    (P.upperHalfPlaneRadiusWeldFromConcreteBishopQuotient
      Q piPositive imagPositive)
quotientMajorantsRegression =
  P.upperHalfPlaneMajorantsFromConcreteBishopQuotient
