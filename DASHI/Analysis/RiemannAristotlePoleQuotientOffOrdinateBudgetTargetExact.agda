module DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateBudgetTargetExact where

------------------------------------------------------------------------
-- POLE-QUOTIENT SIGNED OFF-ORDINATE BUDGET TARGET
--
-- The final lane does not reuse the rank-two determinant taper q.  Its literal
-- zero carrier is the reflection-paired cosine response of the universal
-- pole-quotient taper:
--
--   K(a,delta;u)+K(-a,delta;u)
--     = 4 g_pole(u) cosh(a u) cos(delta u).
--
-- The missing theorem is a signed target-centred bound on that SAME carrier.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

record PoleQuotientOffOrdinateBudgetTarget : Set₁ where
  constructor pole-quotient-off-ordinate-budget-target
  field
    Scalar : Set
    Taper : Set

    OffOrdinateResponse : Taper → Scalar
    OffOrdinateBudget : Taper → Scalar
    _≤_ : Scalar → Scalar → Set

    universalPoleQuotientTaper : Taper

    signedOffOrdinateUpper :
      OffOrdinateResponse universalPoleQuotientTaper
      ≤ OffOrdinateBudget universalPoleQuotientTaper

open PoleQuotientOffOrdinateBudgetTarget public

record PoleQuotientOffOrdinateBudgetBoundary : Set where
  constructor pole-quotient-off-ordinate-budget-boundary
  field
    reflectionPairOddChannelAlreadyCancelled : Bool
    reflectionPairOddChannelAlreadyCancelledIsTrue :
      reflectionPairOddChannelAlreadyCancelled ≡ true

    targetCenteredCosinePhaseRetained : Bool
    targetCenteredCosinePhaseRetainedIsTrue :
      targetCenteredCosinePhaseRetained ≡ true

    absoluteWStyleMajorantAcceptedAsPreferredClosure : Bool
    absoluteWStyleMajorantAcceptedAsPreferredClosureIsFalse :
      absoluteWStyleMajorantAcceptedAsPreferredClosure ≡ false

    rankTwoDeterminantTaperAcceptedWithoutTransport : Bool
    rankTwoDeterminantTaperAcceptedWithoutTransportIsFalse :
      rankTwoDeterminantTaperAcceptedWithoutTransport ≡ false

    literalPoleQuotientSignedOffOrdinateBudgetClosed : Bool
    literalPoleQuotientSignedOffOrdinateBudgetClosedIsFalse :
      literalPoleQuotientSignedOffOrdinateBudgetClosed ≡ false

    requiredTheorem : String

canonicalPoleQuotientOffOrdinateBudgetBoundary :
  PoleQuotientOffOrdinateBudgetBoundary
canonicalPoleQuotientOffOrdinateBudgetBoundary =
  pole-quotient-off-ordinate-budget-boundary
    true refl
    true refl
    false refl
    false refl
    false refl
    "On the exact universal pole-quotient taper g_pole, bound the signed reflection-paired off-ordinate response whose kernel is 4*g_pole(u)*cosh(a*u)*cos((b-t)*u), retaining target-centred cosine cancellation and producing B_off^pole compatible with B_off^pole + B_Gamma < M_cluster^pole."
