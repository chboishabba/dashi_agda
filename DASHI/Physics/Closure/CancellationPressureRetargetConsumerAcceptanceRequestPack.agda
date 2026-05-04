module DASHI.Physics.Closure.CancellationPressureRetargetConsumerAcceptanceRequestPack where

-- W9h: provider-facing request pack for the W9 retarget consumer
-- acceptance lane.
--
-- This module packages the missing interface and acceptance-receipt fields
-- named by W9f/W9g.  It does not construct a RetargetConsumerInterface, a
-- CancellationPressureRetargetConsumerAcceptanceReceipt, a route-around
-- acceptance, an admissible quadratic, a canonical Qcore, or
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

data RetargetConsumerAcceptanceProviderArtifact : Set where
  providerMustSupplyRetargetConsumerInterface :
    RetargetConsumerAcceptanceProviderArtifact
  providerMustSupplyAcceptanceReceipt :
    RetargetConsumerAcceptanceProviderArtifact

canonicalProviderArtifacts :
  List RetargetConsumerAcceptanceProviderArtifact
canonicalProviderArtifacts =
  providerMustSupplyRetargetConsumerInterface
  ∷ providerMustSupplyAcceptanceReceipt
  ∷ []

record RetargetConsumerAcceptanceRequestPack : Setω where
  field
    currentStatus :
      RetargetConsumerAcceptanceRequestStatus

    sourceDiagnostic :
      W9g.CancellationPressureRetargetConsumerSourceDiagnostic

    retargetReceipt :
      W9.PressureCompatibleTargetWithQcoreBoundaryReceipt

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

    obligationMissingFieldsMatchW9f :
      obligationMissingFields
      ≡
      W9f.missingDownstreamConsumerAcceptance
      ∷ W9f.missingTheoremConsumerRouteChange
      ∷ []

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
        blockedAwaitingRetargetConsumerProvider
    ; sourceDiagnostic =
        W9g.currentCancellationPressureRetargetConsumerSourceDiagnostic
    ; retargetReceipt =
        W9.canonicalPairPressureRetargetReceipt
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
    ; obligationMissingFieldsMatchW9f =
        W9g.CancellationPressureRetargetConsumerSourceDiagnostic.obligationMissingFieldsMatchW9f
          W9g.currentCancellationPressureRetargetConsumerSourceDiagnostic
    ; preservedBoundaries =
        W9g.CancellationPressureRetargetConsumerSourceDiagnostic.preservedBoundaries
          W9g.currentCancellationPressureRetargetConsumerSourceDiagnostic
    ; preservedBoundariesMatchW9f =
        W9g.CancellationPressureRetargetConsumerSourceDiagnostic.preservedBoundariesMatchW9f
          W9g.currentCancellationPressureRetargetConsumerSourceDiagnostic
    ; providerRequiredInterfaceFields =
        "acceptsRetargetReceipt : PressureCompatibleTargetWithQcoreBoundaryReceipt -> Set"
        ∷ "acceptanceIsNonPromoting : RetargetConsumerBoundary"
        ∷ []
    ; providerRequiredReceiptFields =
        "acceptsSelectedPressureCompatibleRoute"
        ∷ "acceptsPressureBridgeMatchedBoundary"
        ∷ "preservesNonQcoreBoundary"
        ∷ "acknowledgesRetargetNonPromotion"
        ∷ "downstreamConsumerAcceptance"
        ∷ "downstreamAcceptanceBoundary"
        ∷ []
    ; providerInstructions =
        "Provider must supply a concrete RetargetConsumerInterface for canonicalPairPressureRetargetReceipt"
        ∷ "Provider must supply CancellationPressureRetargetConsumerAcceptanceReceipt for that interface and receipt"
        ∷ "Provider must prove downstreamAcceptanceBoundary equals noCancellationPressureCompatibilityPromotion"
        ∷ "Provider must either accept the retarget for a downstream theorem consumer or provide an explicit theorem route change"
        ∷ []
    ; noPromotionBoundary =
        "This request pack does not construct RetargetConsumerInterface"
        ∷ "This request pack does not construct CancellationPressureRetargetConsumerAcceptanceReceipt"
        ∷ "This request pack does not replace or route around CancellationPressureCompatibility"
        ∷ "This request pack does not assert canonical Qcore or admissible-quadratic promotion"
        ∷ []
    ; strictBlockerImpact =
        "W9 remains blocked: no retarget consumer interface source exists in repo"
        ∷ "W9 remains blocked: no retarget consumer acceptance receipt source exists in repo"
        ∷ "The pressure-compatible retarget remains non-Qcore and non-promoting"
        ∷ "The next admissible move is a downstream provider receipt or explicit theorem route change"
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
