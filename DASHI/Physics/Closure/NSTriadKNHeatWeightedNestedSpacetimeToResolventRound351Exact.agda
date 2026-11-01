module DASHI.Physics.Closure.NSTriadKNHeatWeightedNestedSpacetimeToResolventRound351Exact where

------------------------------------------------------------------------
-- ROUND351 / BIDI: R301 SPACETIME PAYMENT FEEDS THE EXISTING R300 CONSUMER
--
-- R301 already owns the exact downstream shape for a paid heat-weighted nested
-- forcing mass:
--
--   spacetimeForcingMass <= spacetimeUpperBound.
--
-- R300 already owns the integrated Young-absorption consumer.  If the
-- pre-payment remainder is bounded by
--
--   absorbedAmplitudeContribution + spacetimeForcingMass,
--
-- then monotonicity replaces the physical forcing mass by the certified R301
-- upper bound and directly inhabits R300.IntegratedResolventAbsorptionLeaf.
-- No new spacetime or Young ontology is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _+_; _≤_)
import Data.Rational.Properties as ℚP

import DASHI.Physics.Closure.NSTriadKNHeatWeightedCommutatorSchurRound301Exact as R301
import DASHI.Physics.Closure.NSTriadKNResolventYoungAbsorptionRound300Exact as R300

nestedFsSpacetimePaymentToResolventAbsorption :
  (P : R301.HeatWeightedNestedCriticalConeSpacetimePayment)
  (absorbedAmplitudeContribution weightedRemainder : ℚ) →
  weightedRemainder
    ≤ absorbedAmplitudeContribution + R301.spacetimeForcingMass P →
  R300.IntegratedResolventAbsorptionLeaf
nestedFsSpacetimePaymentToResolventAbsorption
  P absorbedAmplitudeContribution weightedRemainder remainderBeforePayment = record
  { absorbedAmplitudeContribution = absorbedAmplitudeContribution
  ; forcingContribution = R301.spacetimeUpperBound P
  ; weightedRemainder = weightedRemainder
  ; weightedRemainderBound =
      ℚP.≤-trans
        remainderBeforePayment
        (ℚP.+-mono-≤ ℚP.≤-refl (R301.spacetimeBound P))
  }

round351R301SpacetimePaymentReused : Bool
round351R301SpacetimePaymentReused = true

round351R300IntegratedResolventConsumerReused : Bool
round351R300IntegratedResolventConsumerReused = true

round351OnlyCompositionIsOrderMonotonicity : Bool
round351OnlyCompositionIsOrderMonotonicity = true

round351SpacetimeToResolventAdapterClosed : Bool
round351SpacetimeToResolventAdapterClosed = true

round351SignedGramRemainderPaymentClosed : Bool
round351SignedGramRemainderPaymentClosed = false

round351PackageAClosed : Bool
round351PackageAClosed = false

round351ClayPromotion : Bool
round351ClayPromotion = false

round351SpacetimeToResolventAdapterClosedIsTrue :
  round351SpacetimeToResolventAdapterClosed ≡ true
round351SpacetimeToResolventAdapterClosedIsTrue = refl

round351PackageAClosedIsFalse : round351PackageAClosed ≡ false
round351PackageAClosedIsFalse = refl

round351ClayPromotionIsFalse : round351ClayPromotion ≡ false
round351ClayPromotionIsFalse = refl
