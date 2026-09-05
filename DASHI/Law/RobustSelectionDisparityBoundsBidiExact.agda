module DASHI.Law.RobustSelectionDisparityBoundsBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Law.PartialIdentificationMissingnessBoundsExact as Bounds
import DASHI.Law.ExactIntervalRatioSeparatorExact as Exact

------------------------------------------------------------------------
-- Robust disparity means the ordering survives every admissible allocation
-- represented by the bound surface.
------------------------------------------------------------------------

record RobustPositiveDisparityReceipt (a b : Bounds.RatioBounds) : Set where
  constructor robustPositiveDisparityReceipt
  field
    worstCaseOrderingReference : String
    allAdmissibleAllocationsPreservePositiveOrdering : Bool
    allAdmissibleAllocationsPreservePositiveOrderingIsTrue :
      allAdmissibleAllocationsPreservePositiveOrdering ≡ true

open RobustPositiveDisparityReceipt public

record RobustNegativeDisparityReceipt (a b : Bounds.RatioBounds) : Set where
  constructor robustNegativeDisparityReceipt
  field
    worstCaseOrderingReference : String
    allAdmissibleAllocationsPreserveNegativeOrdering : Bool
    allAdmissibleAllocationsPreserveNegativeOrderingIsTrue :
      allAdmissibleAllocationsPreserveNegativeOrdering ≡ true

open RobustNegativeDisparityReceipt public

record OverlapReceipt (a b : Bounds.RatioBounds) : Set where
  constructor overlapReceipt
  field
    admissibleOrderingCanReverse : Bool
    admissibleOrderingCanReverseIsTrue : admissibleOrderingCanReverse ≡ true
    overlapReference : String

open OverlapReceipt public

------------------------------------------------------------------------
-- Consumer-specific promotion status.
------------------------------------------------------------------------

data RobustDisparityConclusion : Set where
  robustPositive robustNegative unidentified : RobustDisparityConclusion

record RobustDisparitySurface : Set where
  constructor robustDisparitySurface
  field
    groupA groupB : Bounds.RatioBounds
    conclusion : RobustDisparityConclusion
    conclusionReference : String

open RobustDisparitySurface public

------------------------------------------------------------------------
-- Exact arithmetic now derives the conclusion; no trusted ordering Boolean is
-- needed at this seam.  Malformed bounds fail closed to unidentified.
------------------------------------------------------------------------

derivedConclusion : Bounds.RatioBounds → Bounds.RatioBounds → RobustDisparityConclusion
derivedConclusion a b with Exact.classifyRatioBounds a b
... | Exact.arithmeticRobustPositive = robustPositive
... | Exact.arithmeticRobustNegative = robustNegative
... | Exact.arithmeticUnidentified = unidentified
... | Exact.malformedBounds = unidentified

deriveRobustSurface : Bounds.RatioBounds → Bounds.RatioBounds → RobustDisparitySurface
deriveRobustSurface a b = robustDisparitySurface a b (derivedConclusion a b)
  "derived by exact interval cross multiplication; malformed/overlap fail closed"

canonicalDerivedPositive :
  conclusion (deriveRobustSurface Exact.canonicalA Exact.canonicalSeparatedB) ≡ robustPositive
canonicalDerivedPositive = refl

canonicalDerivedOverlapUnidentified :
  conclusion (deriveRobustSurface Exact.canonicalA Exact.canonicalOverlapB) ≡ unidentified
canonicalDerivedOverlapUnidentified = refl

canonicalMalformedFailsClosed :
  conclusion (deriveRobustSurface Exact.zeroDenominatorBounds Exact.canonicalSeparatedB) ≡ unidentified
canonicalMalformedFailsClosed = refl

------------------------------------------------------------------------
-- BIDI gate.
------------------------------------------------------------------------

data RobustClaim : Set where
  disparityExists disparityDirection pointMagnitude : RobustClaim

data RobustProducer : Set where
  boundSurfaceProducer exactArithmeticSeparatorProducer completeObservationProducer : RobustProducer

reverseRobustClaim : RobustClaim → RobustProducer
reverseRobustClaim disparityExists = exactArithmeticSeparatorProducer
reverseRobustClaim disparityDirection = exactArithmeticSeparatorProducer
reverseRobustClaim pointMagnitude = completeObservationProducer

record RobustPromotionCutset : Set where
  constructor robustPromotionCutset
  field
    boundSurfaceClosed : Bool
    exactArithmeticSeparatorClosed : Bool
    completeObservationClosed : Bool
    cutsetReference : String

open RobustPromotionCutset public

data RobustResidual : Set where
  boundSurfaceResidual exactArithmeticResidual completeObservationResidual robustClosed : RobustResidual

firstRobustResidual : RobustClaim → RobustPromotionCutset → RobustResidual
firstRobustResidual disparityExists c with boundSurfaceClosed c
... | false = boundSurfaceResidual
... | true with exactArithmeticSeparatorClosed c
...   | false = exactArithmeticResidual
...   | true = robustClosed
firstRobustResidual disparityDirection c = firstRobustResidual disparityExists c
firstRobustResidual pointMagnitude c with completeObservationClosed c
... | false = completeObservationResidual
... | true = robustClosed

canonicalRobustButNotPointCutset : RobustPromotionCutset
canonicalRobustButNotPointCutset = robustPromotionCutset true true false
  "bounds and exact cross-multiplication separator close; exact point magnitude remains unavailable"

robustDirectionCanCloseBeforePointMagnitude :
  firstRobustResidual disparityDirection canonicalRobustButNotPointCutset ≡ robustClosed
robustDirectionCanCloseBeforePointMagnitude = refl

pointMagnitudeStillRequiresCompleteObservation :
  firstRobustResidual pointMagnitude canonicalRobustButNotPointCutset ≡ completeObservationResidual
pointMagnitudeStillRequiresCompleteObservation = refl

record RobustDisparityBoundary : Set where
  constructor robustDisparityBoundary
  field
    missingnessPreventsEverySubstantiveConclusion : Bool
    missingnessPreventsEverySubstantiveConclusionIsFalse :
      missingnessPreventsEverySubstantiveConclusion ≡ false
    robustDirectionEqualsExactMagnitude : Bool
    robustDirectionEqualsExactMagnitudeIsFalse :
      robustDirectionEqualsExactMagnitude ≡ false
    overlappingBoundsMayBePromotedToRobustDisparity : Bool
    overlappingBoundsMayBePromotedToRobustDisparityIsFalse :
      overlappingBoundsMayBePromotedToRobustDisparity ≡ false
    trustedOrderingFlagStillRequired : Bool
    trustedOrderingFlagStillRequiredIsFalse : trustedOrderingFlagStillRequired ≡ false

canonicalRobustDisparityBoundary : RobustDisparityBoundary
canonicalRobustDisparityBoundary = robustDisparityBoundary false refl false refl false refl false refl
