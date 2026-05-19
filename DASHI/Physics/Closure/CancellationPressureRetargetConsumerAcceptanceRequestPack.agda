module DASHI.Physics.Closure.CancellationPressureRetargetConsumerAcceptanceRequestPack where

-- W9h: provider-facing request pack for the W9 retarget consumer
-- acceptance lane.
--
-- This module now records the local weighted-support retarget acceptance and
-- packages the remaining theorem-consumer route-change need named by W9f/W9g.
-- It does not construct a route-around theorem consumer, an admissible
-- quadratic, a canonical Qcore, or
-- CancellationPressureCompatibility.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.CancellationPressureCompatibilityNextObligation as W9
import DASHI.Physics.Closure.CancellationPressureRetargetConsumerObligation as W9f
import DASHI.Physics.Closure.CancellationPressureRetargetConsumerSourceDiagnostic as W9g

data RetargetConsumerAcceptanceRequestStatus : Set where
  blockedAwaitingRetargetConsumerProvider :
    RetargetConsumerAcceptanceRequestStatus
  retargetAcceptedAwaitingTheoremConsumerRouteChange :
    RetargetConsumerAcceptanceRequestStatus

data RetargetConsumerAcceptanceProviderArtifact : Set where
  providerMustSupplyRetargetConsumerInterface :
    RetargetConsumerAcceptanceProviderArtifact
  providerMustSupplyAcceptanceReceipt :
    RetargetConsumerAcceptanceProviderArtifact
  providerMustSupplyTheoremConsumerRouteChange :
    RetargetConsumerAcceptanceProviderArtifact

canonicalProviderArtifacts :
  List RetargetConsumerAcceptanceProviderArtifact
canonicalProviderArtifacts =
  providerMustSupplyTheoremConsumerRouteChange
  ∷ []

record RetargetConsumerAcceptanceRequestPack : Setω where
  field
    currentStatus :
      RetargetConsumerAcceptanceRequestStatus

    sourceDiagnostic :
      W9g.CancellationPressureRetargetConsumerSourceDiagnostic

    acceptedRetargetReceipt :
      W9g.W9RetargetConsumerLeReceiptDiagnostic

    retargetReceipt :
      W9.PressureCompatibleTargetWithQcoreBoundaryReceipt

    currentClosureObstruction :
      W9.Dim15DeltaToQuadraticClosureObstruction

    closureStatus :
      W9.W9Dim15ClosureStatus

    closureStatusIsCurrent :
      closureStatus
      ≡
      W9.dim15RoutesExhaustedRetargetAwaitingConsumer

    exactRetargetReceiptName :
      String

    selectedRoute :
      W9.W9NextTypedRoute

    selectedRouteIsCanonicalRetarget :
      selectedRoute
      ≡
      W9.supplyPressureCompatibleTargetWithQcoreBoundary

    requiredInterfaceName :
      String

    requiredReceiptName :
      String

    requiredProviderArtifacts :
      List RetargetConsumerAcceptanceProviderArtifact

    requiredProviderArtifactsAreCanonical :
      requiredProviderArtifacts ≡ canonicalProviderArtifacts

    missingSourceFields :
      List W9g.RetargetConsumerSourceMissingField

    missingSourceFieldsAreCurrent :
      missingSourceFields
      ≡
      W9g.currentRetargetConsumerSourceMissingFields

    obligationMissingFields :
      List W9f.RetargetConsumerMissingField

    obligationMissingFieldsAreCurrent :
      obligationMissingFields
      ≡
      W9g.currentRetargetConsumerObligationMissingFields

    preservedBoundaries :
      List W9f.RetargetConsumerBoundary

    preservedBoundariesMatchW9f :
      preservedBoundaries
      ≡
      W9f.pressureCompatibleButNonQcore
      ∷ W9f.noAdmissibleQuadraticPromotion
      ∷ W9f.noCancellationPressureCompatibilityPromotion
      ∷ []

    providerRequiredInterfaceFields :
      List String

    providerRequiredReceiptFields :
      List String

    providerInstructions :
      List String

    noPromotionBoundary :
      List String

    strictBlockerImpact :
      List String

canonicalRetargetConsumerAcceptanceRequestPack :
  RetargetConsumerAcceptanceRequestPack
canonicalRetargetConsumerAcceptanceRequestPack =
  record
    { currentStatus =
        retargetAcceptedAwaitingTheoremConsumerRouteChange
    ; sourceDiagnostic =
        W9g.currentCancellationPressureRetargetConsumerSourceDiagnostic
    ; acceptedRetargetReceipt =
        W9g.currentW9RetargetConsumerLeReceiptDiagnostic
    ; retargetReceipt =
        W9.canonicalPairPressureRetargetReceipt
    ; currentClosureObstruction =
        W9.canonical15DeltaToQuadraticClosureObstruction
    ; closureStatus =
        W9.Dim15DeltaToQuadraticClosureObstruction.closureStatus
          W9.canonical15DeltaToQuadraticClosureObstruction
    ; closureStatusIsCurrent =
        refl
    ; exactRetargetReceiptName =
        "DASHI.Physics.Closure.CancellationPressureCompatibilityNextObligation.canonicalPairPressureRetargetReceipt"
    ; selectedRoute =
        W9.PressureCompatibleTargetWithQcoreBoundaryReceipt.selectedNextRoute
          W9.canonicalPairPressureRetargetReceipt
    ; selectedRouteIsCanonicalRetarget =
        refl
    ; requiredInterfaceName =
        W9g.CancellationPressureRetargetConsumerSourceDiagnostic.requiredInterface
          W9g.currentCancellationPressureRetargetConsumerSourceDiagnostic
    ; requiredReceiptName =
        W9g.CancellationPressureRetargetConsumerSourceDiagnostic.requiredReceipt
          W9g.currentCancellationPressureRetargetConsumerSourceDiagnostic
    ; requiredProviderArtifacts =
        canonicalProviderArtifacts
    ; requiredProviderArtifactsAreCanonical =
        refl
    ; missingSourceFields =
        W9g.CancellationPressureRetargetConsumerSourceDiagnostic.missingSourceFields
          W9g.currentCancellationPressureRetargetConsumerSourceDiagnostic
    ; missingSourceFieldsAreCurrent =
        refl
    ; obligationMissingFields =
        W9g.CancellationPressureRetargetConsumerSourceDiagnostic.obligationMissingFields
          W9g.currentCancellationPressureRetargetConsumerSourceDiagnostic
    ; obligationMissingFieldsAreCurrent =
        W9g.CancellationPressureRetargetConsumerSourceDiagnostic.obligationMissingFieldsAreCurrent
          W9g.currentCancellationPressureRetargetConsumerSourceDiagnostic
    ; preservedBoundaries =
        W9g.CancellationPressureRetargetConsumerSourceDiagnostic.preservedBoundaries
          W9g.currentCancellationPressureRetargetConsumerSourceDiagnostic
    ; preservedBoundariesMatchW9f =
        W9g.CancellationPressureRetargetConsumerSourceDiagnostic.preservedBoundariesMatchW9f
          W9g.currentCancellationPressureRetargetConsumerSourceDiagnostic
    ; providerRequiredInterfaceFields =
        "Already supplied by W9WeightedSupportRetargetConsumerReceipt.weightedSupportRetargetConsumer"
        ∷ "acceptsRetargetReceipt uses weightedMaxPressure <= weightedSupport"
        ∷ []
    ; providerRequiredReceiptFields =
        "Already supplied by W9WeightedSupportRetargetConsumerReceipt.weightedSupportRetargetAcceptanceReceipt"
        ∷ "Remaining needed interface is theorem-consumer route change, not another acceptance receipt"
        ∷ []
    ; providerInstructions =
        "Retarget consumer acceptance is locally supplied by the weighted-support <= receipt"
        ∷ "Provider must supply an explicit theorem-consumer route change before this retarget can route around CancellationPressureCompatibility"
        ∷ "The route change must preserve the non-Qcore and no-admissible-quadratic boundaries"
        ∷ []
    ; noPromotionBoundary =
        "This request pack records the existing weighted-support RetargetConsumerInterface"
        ∷ "This request pack records the existing weighted-support CancellationPressureRetargetConsumerAcceptanceReceipt"
        ∷ "This request pack does not construct a theorem-consumer route change"
        ∷ "This request pack does not replace or route around CancellationPressureCompatibility"
        ∷ "This request pack does not assert canonical Qcore or admissible-quadratic promotion"
        ∷ []
    ; strictBlockerImpact =
        "W9 remains blocked: no theorem-consumer route change exists for the accepted non-Qcore retarget"
        ∷ "The pressure-compatible retarget remains non-Qcore and non-promoting"
        ∷ "The next admissible move is an explicit theorem route change or the original equality witness route"
        ∷ []
    }

canonicalRequestPackMissingSourceFields :
  List W9g.RetargetConsumerSourceMissingField
canonicalRequestPackMissingSourceFields =
  RetargetConsumerAcceptanceRequestPack.missingSourceFields
    canonicalRetargetConsumerAcceptanceRequestPack

canonicalRequestPackPreservedBoundaries :
  List W9f.RetargetConsumerBoundary
canonicalRequestPackPreservedBoundaries =
  RetargetConsumerAcceptanceRequestPack.preservedBoundaries
    canonicalRetargetConsumerAcceptanceRequestPack

canonicalRequestPackNoPromotionBoundary :
  List String
canonicalRequestPackNoPromotionBoundary =
  RetargetConsumerAcceptanceRequestPack.noPromotionBoundary
    canonicalRetargetConsumerAcceptanceRequestPack
