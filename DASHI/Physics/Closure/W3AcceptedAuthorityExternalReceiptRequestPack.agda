module DASHI.Physics.Closure.W3AcceptedAuthorityExternalReceiptRequestPack where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.W3AcceptedAuthorityExternalReceiptObligation as EXT
import DASHI.Physics.Closure.W3AcceptedAuthorityRouteNarrowing as Route
import DASHI.Physics.Closure.W3AcceptedEmpiricalAuthorityGate as AUTH
import DASHI.Physics.Closure.W3EmpiricalTargetPromotionBridgeObligation as W3

------------------------------------------------------------------------
-- W3p accepted-authority external receipt request pack.
--
-- This module packages the provider-facing inputs needed for W3 accepted
-- authority.  It constructs no W3AcceptedEvidenceAuthorityToken, no
-- W3EvidenceBackedEmpiricalTarget, no B4 empirical promotion, no origin
-- promotion, no empirical adequacy theorem, and no accepted-authority receipt.

data W3AcceptedAuthorityExternalReceiptRequestPackStatus : Set where
  blockedAwaitingAcceptedAuthorityExternalReceipt :
    W3AcceptedAuthorityExternalReceiptRequestPackStatus

data W3AcceptedAuthorityProviderMissingField : Set where
  missingAcceptedEvidenceAuthorityToken :
    W3AcceptedAuthorityProviderMissingField
  missingEvidenceBackedEmpiricalTarget :
    W3AcceptedAuthorityProviderMissingField
  missingEvidenceTargetAuthorityEquality :
    W3AcceptedAuthorityProviderMissingField
  missingB4EmpiricalPromotion :
    W3AcceptedAuthorityProviderMissingField
  missingOriginReceiptPromotion :
    W3AcceptedAuthorityProviderMissingField
  missingBridgeObligations :
    W3AcceptedAuthorityProviderMissingField
  missingBridgeTargetEvidenceEquality :
    W3AcceptedAuthorityProviderMissingField

record W3AcceptedAuthorityProviderPayloadRequest : Setω where
  field
    currentExternalStatus :
      EXT.W3AcceptedAuthorityExternalReceiptCurrentStatus

    routeDiagnostic :
      Route.W3AcceptedAuthorityRouteCurrentDiagnostic

    bridgeObligationReceipt :
      W3.W3EmpiricalTargetPromotionBridgeObligationReceipt

    externalReceiptStatuses :
      List EXT.W3AcceptedAuthorityExternalReceiptStatus

    externalReceiptStatusesAreCanonical :
      externalReceiptStatuses
      ≡
      EXT.canonicalW3AcceptedAuthorityExternalReceiptStatuses

    externalReceiptStatusesAreCurrent :
      externalReceiptStatuses
      ≡
      EXT.W3AcceptedAuthorityExternalReceiptCurrentStatus.externalReceiptStatuses
        currentExternalStatus

    authorityGateStatuses :
      List AUTH.W3AuthorityGateStatus

    authorityGateStatusesAreCanonical :
      authorityGateStatuses
      ≡
      AUTH.canonicalCurrentW3AcceptedAuthorityStatuses

    authorityGateStatusesAreCurrent :
      authorityGateStatuses
      ≡
      EXT.W3AcceptedAuthorityExternalReceiptCurrentStatus.authorityStatuses
        currentExternalStatus

    routeBlockers :
      List Route.W3AcceptedAuthorityRouteBlocker

    routeBlockersAreCanonical :
      routeBlockers
      ≡
      Route.canonicalW3AcceptedAuthorityRouteBlockers

    routeBlockersAreCurrent :
      routeBlockers
      ≡
      Route.W3AcceptedAuthorityRouteCurrentDiagnostic.currentBlockers
        routeDiagnostic

    missingProviderFields :
      List W3AcceptedAuthorityProviderMissingField

    exactExternalReceiptName :
      String

    exactAuthorityTokenName :
      String

    exactEvidenceBackedTargetName :
      String

    exactB4PromotionName :
      String

    exactOriginPromotionName :
      String

    exactBridgeObligationsName :
      String

    exactReceiptFields :
      List String

    providerInstructions :
      List String

    authorityBoundary :
      List String

    routeBoundary :
      List String

    b4OriginBlockers :
      List String

    nonPromotionBoundary :
      List String

    strictBlockerImpact :
      List String

    impossibleAuthorityHere :
      AUTH.W3AcceptedEvidenceAuthorityToken →
      EXT.W3AcceptedAuthorityExternalReceiptImpossible

    impossibleEvidenceTargetHere :
      AUTH.W3EvidenceBackedEmpiricalTarget →
      EXT.W3AcceptedAuthorityExternalReceiptImpossible

    impossibleExternalReceiptHere :
      EXT.W3AcceptedAuthorityExternalReceipt →
      EXT.W3AcceptedAuthorityExternalReceiptImpossible

canonicalW3AcceptedAuthorityProviderPayloadRequest :
  W3AcceptedAuthorityProviderPayloadRequest
canonicalW3AcceptedAuthorityProviderPayloadRequest =
  record
    { currentExternalStatus =
        EXT.currentW3AcceptedAuthorityExternalReceiptStatus
    ; routeDiagnostic =
        Route.canonicalW3AcceptedAuthorityRouteCurrentDiagnostic
    ; bridgeObligationReceipt =
        W3.canonicalW3EmpiricalTargetPromotionBridgeObligationReceipt
    ; externalReceiptStatuses =
        EXT.canonicalW3AcceptedAuthorityExternalReceiptStatuses
    ; externalReceiptStatusesAreCanonical =
        refl
    ; externalReceiptStatusesAreCurrent =
        refl
    ; authorityGateStatuses =
        AUTH.canonicalCurrentW3AcceptedAuthorityStatuses
    ; authorityGateStatusesAreCanonical =
        refl
    ; authorityGateStatusesAreCurrent =
        refl
    ; routeBlockers =
        Route.canonicalW3AcceptedAuthorityRouteBlockers
    ; routeBlockersAreCanonical =
        refl
    ; routeBlockersAreCurrent =
        refl
    ; missingProviderFields =
        missingAcceptedEvidenceAuthorityToken
        ∷ missingEvidenceBackedEmpiricalTarget
        ∷ missingEvidenceTargetAuthorityEquality
        ∷ missingB4EmpiricalPromotion
        ∷ missingOriginReceiptPromotion
        ∷ missingBridgeObligations
        ∷ missingBridgeTargetEvidenceEquality
        ∷ []
    ; exactExternalReceiptName =
        "DASHI.Physics.Closure.W3AcceptedAuthorityExternalReceiptObligation.W3AcceptedAuthorityExternalReceipt"
    ; exactAuthorityTokenName =
        "DASHI.Physics.Closure.W3AcceptedEmpiricalAuthorityGate.W3AcceptedEvidenceAuthorityToken"
    ; exactEvidenceBackedTargetName =
        "DASHI.Physics.Closure.W3AcceptedEmpiricalAuthorityGate.W3EvidenceBackedEmpiricalTarget"
    ; exactB4PromotionName =
        "DASHI.Physics.Closure.W3EmpiricalTargetPromotionBridgeObligation.B4EmpiricalPromotionObligation"
    ; exactOriginPromotionName =
        "DASHI.Physics.Closure.W3EmpiricalTargetPromotionBridgeObligation.OriginReceiptPromotionObligation"
    ; exactBridgeObligationsName =
        "DASHI.Physics.Closure.W3EmpiricalTargetPromotionBridgeObligation.W3EmpiricalTargetPromotionBridgeObligations"
    ; exactReceiptFields =
        "authorityToken : W3AcceptedEvidenceAuthorityToken"
        ∷ "evidenceBackedEmpiricalTarget : W3EvidenceBackedEmpiricalTarget"
        ∷ "evidenceTargetCarriesAuthority : evidence target authority == authorityToken"
        ∷ "b4EmpiricalPromotion : B4EmpiricalPromotionObligation"
        ∷ "originReceiptPromotion : OriginReceiptPromotionObligation"
        ∷ "bridgeObligations : W3EmpiricalTargetPromotionBridgeObligations"
        ∷ "bridgeTargetMatchesEvidence : bridge empirical target == evidence-backed empirical target"
        ∷ []
    ; providerInstructions =
        "Supply the exact W3AcceptedAuthorityExternalReceipt payload named above; do not replace it with the current surrogate target"
        ∷ "HEP-R55 first response should supply W3AcceptedEvidenceAuthorityToken from an accepted external authority, or return a typed authority-unavailable/mismatch diagnostic"
        ∷ "Authority must be accepted evidence authority, not empirical-only photonuclear summary packaging"
        ∷ "B4 must be empirically promoted from standaloneOnly to admissibleReady"
        ∷ "Origin must be promoted beyond empiricalBlocked through the W8 origin-promotion receipt route"
        ∷ "If the receipt cannot be supplied, return a typed authority/mismatch diagnostic rather than prose"
        ∷ []
    ; authorityBoundary =
        EXT.W3AcceptedAuthorityExternalReceiptCurrentStatus.authorityBoundary
          EXT.currentW3AcceptedAuthorityExternalReceiptStatus
    ; routeBoundary =
        Route.W3AcceptedAuthorityRouteCurrentDiagnostic.routeBoundary
          Route.canonicalW3AcceptedAuthorityRouteCurrentDiagnostic
    ; b4OriginBlockers =
        "B4 shell report remains standaloneOnly, so B4EmpiricalPromotionObligation is unavailable"
        ∷ "Origin observation receipt remains empiricalBlocked, so OriginReceiptPromotionObligation is unavailable"
        ∷ "W8 origin-promotion external receipt remains required before W3 accepted authority can close"
        ∷ []
    ; nonPromotionBoundary =
        "This request pack is a provider-facing handoff only"
        ∷ "It does not construct W3AcceptedEvidenceAuthorityToken"
        ∷ "It does not construct W3EvidenceBackedEmpiricalTarget"
        ∷ "It does not construct B4EmpiricalPromotionObligation"
        ∷ "It does not construct OriginReceiptPromotionObligation"
        ∷ "It does not construct W3AcceptedAuthorityExternalReceipt"
        ∷ "It does not inhabit obs(fixedPoint)=empirical"
        ∷ []
    ; strictBlockerImpact =
        "W3 remains blocked until W3AcceptedAuthorityExternalReceipt is externally supplied"
        ∷ "The first missing provider field is W3AcceptedEvidenceAuthorityToken; HEP-R55 should be external provider engagement only"
        ∷ "Current B4 status remains empirical-standalone, not promoted"
        ∷ "Current origin status remains empiricalBlocked and depends on W8 origin-promotion evidence"
        ∷ "This module only makes the accepted-authority provider handoff typed and auditable"
        ∷ []
    ; impossibleAuthorityHere =
        EXT.W3AcceptedAuthorityExternalReceiptCurrentStatus.acceptedAuthorityTokenUninhabited
          EXT.currentW3AcceptedAuthorityExternalReceiptStatus
    ; impossibleEvidenceTargetHere =
        EXT.W3AcceptedAuthorityExternalReceiptCurrentStatus.evidenceBackedTargetBlockedByAuthority
          EXT.currentW3AcceptedAuthorityExternalReceiptStatus
    ; impossibleExternalReceiptHere =
        EXT.W3AcceptedAuthorityExternalReceiptCurrentStatus.externalReceiptBlockedByAuthority
          EXT.currentW3AcceptedAuthorityExternalReceiptStatus
    }

record W3AcceptedAuthorityExternalReceiptRequestPack : Setω where
  field
    currentStatus :
      W3AcceptedAuthorityExternalReceiptRequestPackStatus

    currentExternalStatus :
      EXT.W3AcceptedAuthorityExternalReceiptCurrentStatus

    routeDiagnostic :
      Route.W3AcceptedAuthorityRouteCurrentDiagnostic

    providerPayloadRequest :
      W3AcceptedAuthorityProviderPayloadRequest

    requiredNextReceipt :
      String

    requiredAuthorityToken :
      String

    requiredB4AndOriginPromotion :
      List String

    consolidatedProviderInstructions :
      List String

    consolidatedNonPromotionBoundary :
      List String

    consolidatedStrictBlockerImpact :
      List String

canonicalW3AcceptedAuthorityExternalReceiptRequestPack :
  W3AcceptedAuthorityExternalReceiptRequestPack
canonicalW3AcceptedAuthorityExternalReceiptRequestPack =
  record
    { currentStatus =
        blockedAwaitingAcceptedAuthorityExternalReceipt
    ; currentExternalStatus =
        EXT.currentW3AcceptedAuthorityExternalReceiptStatus
    ; routeDiagnostic =
        Route.canonicalW3AcceptedAuthorityRouteCurrentDiagnostic
    ; providerPayloadRequest =
        canonicalW3AcceptedAuthorityProviderPayloadRequest
    ; requiredNextReceipt =
        W3AcceptedAuthorityProviderPayloadRequest.exactExternalReceiptName
          canonicalW3AcceptedAuthorityProviderPayloadRequest
    ; requiredAuthorityToken =
        W3AcceptedAuthorityProviderPayloadRequest.exactAuthorityTokenName
          canonicalW3AcceptedAuthorityProviderPayloadRequest
    ; requiredB4AndOriginPromotion =
        W3AcceptedAuthorityProviderPayloadRequest.b4OriginBlockers
          canonicalW3AcceptedAuthorityProviderPayloadRequest
    ; consolidatedProviderInstructions =
        W3AcceptedAuthorityProviderPayloadRequest.providerInstructions
          canonicalW3AcceptedAuthorityProviderPayloadRequest
    ; consolidatedNonPromotionBoundary =
        W3AcceptedAuthorityProviderPayloadRequest.nonPromotionBoundary
          canonicalW3AcceptedAuthorityProviderPayloadRequest
    ; consolidatedStrictBlockerImpact =
        W3AcceptedAuthorityProviderPayloadRequest.strictBlockerImpact
          canonicalW3AcceptedAuthorityProviderPayloadRequest
    }

canonicalW3AcceptedAuthorityExternalReceiptRequestPackStatus :
  W3AcceptedAuthorityExternalReceiptRequestPackStatus
canonicalW3AcceptedAuthorityExternalReceiptRequestPackStatus =
  blockedAwaitingAcceptedAuthorityExternalReceipt
