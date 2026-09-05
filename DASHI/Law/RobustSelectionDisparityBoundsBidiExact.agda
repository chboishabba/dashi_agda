module DASHI.Law.RobustSelectionDisparityBoundsBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Law.PartialIdentificationMissingnessBoundsExact as Bounds

------------------------------------------------------------------------
-- Robust disparity means the ordering survives every admissible allocation
-- represented by the bound surface.  We keep arithmetic comparison receipts
-- explicit rather than hiding them inside a point estimate.
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
-- BIDI gate.
------------------------------------------------------------------------

data RobustClaim : Set where
  disparityExists disparityDirection pointMagnitude : RobustClaim

data RobustProducer : Set where
  boundSurfaceProducer worstCaseOrderingProducer completeObservationProducer : RobustProducer

reverseRobustClaim : RobustClaim → RobustProducer
reverseRobustClaim disparityExists = worstCaseOrderingProducer
reverseRobustClaim disparityDirection = worstCaseOrderingProducer
reverseRobustClaim pointMagnitude = completeObservationProducer

record RobustPromotionCutset : Set where
  constructor robustPromotionCutset
  field
    boundSurfaceClosed : Bool
    worstCaseOrderingClosed : Bool
    completeObservationClosed : Bool
    cutsetReference : String

open RobustPromotionCutset public

data RobustResidual : Set where
  boundSurfaceResidual worstCaseOrderingResidual completeObservationResidual robustClosed : RobustResidual

firstRobustResidual : RobustClaim → RobustPromotionCutset → RobustResidual
firstRobustResidual disparityExists c with boundSurfaceClosed c
... | false = boundSurfaceResidual
... | true with worstCaseOrderingClosed c
...   | false = worstCaseOrderingResidual
...   | true = robustClosed
firstRobustResidual disparityDirection c = firstRobustResidual disparityExists c
firstRobustResidual pointMagnitude c with completeObservationClosed c
... | false = completeObservationResidual
... | true = robustClosed

canonicalRobustButNotPointCutset : RobustPromotionCutset
canonicalRobustButNotPointCutset = robustPromotionCutset true true false
  "bounds and worst-case ordering close; exact point magnitude remains unavailable"

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

canonicalRobustDisparityBoundary : RobustDisparityBoundary
canonicalRobustDisparityBoundary = robustDisparityBoundary false refl false refl false refl
