module DASHI.Physics.Closure.CancellationPressureRetargetConsumerObligation where

-- W9f: downstream consumer obligation for the W9e pressure-compatible
-- retarget receipt.
--
-- This module does not promote CancellationPressureCompatibility.  It names
-- the exact downstream acceptance receipt required before the W9e canonical
-- pair-pressure retarget can replace, or route around, existing theorem
-- consumers of CancellationPressureCompatibility.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.CancellationPressureCompatibilityNextObligation as W9

data RetargetConsumerBoundary : Set where
  pressureCompatibleButNonQcore :
    RetargetConsumerBoundary
  noAdmissibleQuadraticPromotion :
    RetargetConsumerBoundary
  noCancellationPressureCompatibilityPromotion :
    RetargetConsumerBoundary

data RetargetConsumerMissingField : Set where
  missingDownstreamConsumerAcceptance :
    RetargetConsumerMissingField
  missingTheoremConsumerRouteChange :
    RetargetConsumerMissingField

record RetargetConsumerInterface : Setω where
  field
    acceptsRetargetReceipt :
      W9.PressureCompatibleTargetWithQcoreBoundaryReceipt →
      Set

    acceptanceIsNonPromoting :
      RetargetConsumerBoundary

record CancellationPressureRetargetConsumerAcceptanceReceipt
  (consumer : RetargetConsumerInterface)
  (receipt : W9.PressureCompatibleTargetWithQcoreBoundaryReceipt) :
  Setω where
  field
    acceptsSelectedPressureCompatibleRoute :
      W9.PressureCompatibleTargetWithQcoreBoundaryReceipt.selectedNextRoute
        receipt
      ≡
      W9.supplyPressureCompatibleTargetWithQcoreBoundary

    acceptsPressureBridgeMatchedBoundary :
      W9.PressureCompatibleTargetWithQcoreBoundaryReceipt.pressureTargetMatchesBridgeAtBoundary
        receipt
      ≡
      W9.PressureCompatibleTargetWithQcoreBoundaryReceipt.pressureTargetMatchesBridgeAtBoundary
        receipt

    preservesNonQcoreBoundary :
      W9.PressureCompatibleTargetWithQcoreBoundaryReceipt.pressureTargetDiffersFromCanonicalQcoreAtBoundary
        receipt
      ≡
      W9.PressureCompatibleTargetWithQcoreBoundaryReceipt.pressureTargetDiffersFromCanonicalQcoreAtBoundary
        receipt

    acknowledgesRetargetNonPromotion :
      W9.PressureCompatibleTargetWithQcoreBoundaryReceipt.nonPromotionBoundary
        receipt
      ≡
      W9.retargetMustNotClaimCanonicalQcore

    downstreamConsumerAcceptance :
      RetargetConsumerInterface.acceptsRetargetReceipt consumer receipt

    downstreamAcceptanceBoundary :
      RetargetConsumerInterface.acceptanceIsNonPromoting consumer
      ≡
      noCancellationPressureCompatibilityPromotion

record CanonicalPairPressureRetargetConsumerObligation : Setω where
  field
    retargetReceipt :
      W9.PressureCompatibleTargetWithQcoreBoundaryReceipt

    requiredConsumerInterface :
      RetargetConsumerInterface

    missingFields :
      List RetargetConsumerMissingField

    preservedBoundaries :
      List RetargetConsumerBoundary

    blockerImpact :
      List String

canonicalPairPressureRetargetConsumerObligation :
  RetargetConsumerInterface →
  CanonicalPairPressureRetargetConsumerObligation
canonicalPairPressureRetargetConsumerObligation consumer =
  record
    { retargetReceipt =
        W9.canonicalPairPressureRetargetReceipt
    ; requiredConsumerInterface =
        consumer
    ; missingFields =
        missingDownstreamConsumerAcceptance
        ∷ missingTheoremConsumerRouteChange
        ∷ []
    ; preservedBoundaries =
        pressureCompatibleButNonQcore
        ∷ noAdmissibleQuadraticPromotion
        ∷ noCancellationPressureCompatibilityPromotion
        ∷ []
    ; blockerImpact =
        "W9e canonicalPairPressureRetargetReceipt is available to consumers"
        ∷ "A downstream consumer must inhabit CancellationPressureRetargetConsumerAcceptanceReceipt before the retarget can replace or route around CancellationPressureCompatibility"
        ∷ "The retarget receipt remains pressure-compatible but non-Qcore and does not assert admissible-quadratic closure"
        ∷ "W9 remains blocked for theorem closure until a consumer acceptance receipt or theorem route change lands"
        ∷ []
    }

retargetConsumerAcceptanceRequiredBeforeRouteAround :
  (consumer : RetargetConsumerInterface) →
  Setω
retargetConsumerAcceptanceRequiredBeforeRouteAround consumer =
  CancellationPressureRetargetConsumerAcceptanceReceipt
    consumer
    W9.canonicalPairPressureRetargetReceipt
