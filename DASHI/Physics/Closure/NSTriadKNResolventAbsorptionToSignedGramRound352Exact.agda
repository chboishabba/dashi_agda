module DASHI.Physics.Closure.NSTriadKNResolventAbsorptionToSignedGramRound352Exact where

------------------------------------------------------------------------
-- ROUND352 / BIDI: R300 PAID REMAINDER FEEDS R303 DEFINITIONALLY
--
-- R300.IntegratedResolventAbsorptionLeaf already says
--
--   weightedRemainder
--     <= absorbedAmplitudeContribution + forcingContribution.
--
-- R303.SignedGramFluxPayment asks for exactly a remainder integral and an upper
-- bound, alongside the independently paid initial/terminal flux terms.
-- Therefore the R300 remainder can be used directly as R303's
-- weightedRemainderIntegral and its two-term upper bound as remainderUpper.
-- No new remainder estimate is needed between these owners.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _+_; _≤_)

import DASHI.Physics.Closure.NSTriadKNResolventYoungAbsorptionRound300Exact as R300
import DASHI.Physics.Closure.NSTriadKNSignedGramFluxPaymentRound303Exact as R303

resolventAbsorptionToSignedGramPayment :
  (R : R300.IntegratedResolventAbsorptionLeaf)
  (signedGramIntegral initialFlux terminalNegativeFlux : ℚ)
  (initialUpper terminalUpper : ℚ)
  (fluxIdentity :
    signedGramIntegral
    ≡ initialFlux + terminalNegativeFlux + R300.weightedRemainder R)
  (initialPaid : initialFlux ≤ initialUpper)
  (terminalPaid : terminalNegativeFlux ≤ terminalUpper) →
  R303.SignedGramFluxPayment
resolventAbsorptionToSignedGramPayment
  R signedGramIntegral initialFlux terminalNegativeFlux
  initialUpper terminalUpper fluxIdentity initialPaid terminalPaid = record
  { signedGramIntegral = signedGramIntegral
  ; initialFlux = initialFlux
  ; terminalNegativeFlux = terminalNegativeFlux
  ; weightedRemainderIntegral = R300.weightedRemainder R
  ; initialUpper = initialUpper
  ; terminalUpper = terminalUpper
  ; remainderUpper =
      R300.absorbedAmplitudeContribution R + R300.forcingContribution R
  ; fluxIdentity = fluxIdentity
  ; initialPaid = initialPaid
  ; terminalPaid = terminalPaid
  ; remainderPaid = R300.weightedRemainderBound R
  }

round352R300WeightedRemainderUsedDirectly : Bool
round352R300WeightedRemainderUsedDirectly = true

round352R303SignedGramCompilerReused : Bool
round352R303SignedGramCompilerReused = true

round352NoIntermediateRemainderOntology : Bool
round352NoIntermediateRemainderOntology = true

round352ResolventToSignedGramAdapterClosed : Bool
round352ResolventToSignedGramAdapterClosed = true

round352R293ConsumptionClosed : Bool
round352R293ConsumptionClosed = false

round352PackageAClosed : Bool
round352PackageAClosed = false

round352ClayPromotion : Bool
round352ClayPromotion = false

round352ResolventToSignedGramAdapterClosedIsTrue :
  round352ResolventToSignedGramAdapterClosed ≡ true
round352ResolventToSignedGramAdapterClosedIsTrue = refl

round352PackageAClosedIsFalse : round352PackageAClosed ≡ false
round352PackageAClosedIsFalse = refl

round352ClayPromotionIsFalse : round352ClayPromotion ≡ false
round352ClayPromotionIsFalse = refl
