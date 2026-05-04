module DASHI.Physics.Closure.OriginReceiptPromotionExternalRequestPack where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.OriginReceiptPromotionExternalObligation as W8

------------------------------------------------------------------------
-- W8d external request pack.
--
-- This module packages the current W8 origin-promotion obligation into a
-- provider-facing handoff surface.  It records the missing evidence and
-- receipt names only; it constructs no empirical adequacy bridge, no
-- promoted-status authority, no OriginReceiptPromotionExternalReceipt, and no
-- origin promotion.

data OriginReceiptPromotionExternalRequestPackStatus : Set where
  blockedAwaitingExternalOriginPromotionReceipt :
    OriginReceiptPromotionExternalRequestPackStatus

record OriginReceiptPromotionExternalRequestPack : Setω where
  field
    currentStatus :
      W8.OriginReceiptPromotionExternalCurrentStatus

    sourceDiagnostic :
      W8.CurrentOriginAuthoritySourceDiagnostic

    sourceScanResult :
      W8.OriginEmpiricalAuthoritySourceScanResult

    sourceScanResultIsCanonical :
      sourceScanResult
      ≡
      W8.noCurrentOriginAuthoritySourceFound

    blockedFields :
      List W8.OriginReceiptPromotionExternalBlockedField

    blockedFieldsAreCanonical :
      blockedFields
      ≡
      W8.canonicalOriginReceiptPromotionExternalBlockedFields

    blockedFieldsAreCurrentStatus :
      blockedFields
      ≡
      W8.OriginReceiptPromotionExternalCurrentStatus.blockedFields
        currentStatus

    missingEvidenceKinds :
      List W8.OriginPromotionExternalReceiptNeeded

    exactExternalReceiptName :
      String

    exactEvidenceCarrierName :
      String

    exactPromotedStatusReceiptName :
      String

    exactAuthorityTokenName :
      String

    exactBlockedReceiptFields :
      List String

    requiredProviderEvidence :
      List String

    providerInstructions :
      List String

    sourceDiagnosticSummary :
      List String

    nonPromotionBoundary :
      List String

    strictBlockerImpact :
      List String

canonicalOriginReceiptPromotionExternalRequestPack :
  OriginReceiptPromotionExternalRequestPack
canonicalOriginReceiptPromotionExternalRequestPack =
  record
    { currentStatus =
        W8.canonicalOriginReceiptPromotionExternalCurrentStatus
    ; sourceDiagnostic =
        W8.canonicalCurrentOriginAuthoritySourceDiagnostic
    ; sourceScanResult =
        W8.CurrentOriginAuthoritySourceDiagnostic.sourceScanResult
          W8.canonicalCurrentOriginAuthoritySourceDiagnostic
    ; sourceScanResultIsCanonical =
        refl
    ; blockedFields =
        W8.canonicalOriginReceiptPromotionExternalBlockedFields
    ; blockedFieldsAreCanonical =
        refl
    ; blockedFieldsAreCurrentStatus =
        refl
    ; missingEvidenceKinds =
        W8.needExternalOriginPromotedEmpiricalStatusAuthority
        ∷ W8.needOriginEmpiricalAdequacyBridgeForCurrentReceipt
        ∷ []
    ; exactExternalReceiptName =
        "DASHI.Physics.Closure.OriginReceiptPromotionExternalObligation.OriginReceiptPromotionExternalReceipt"
    ; exactEvidenceCarrierName =
        "DASHI.Physics.Closure.OriginReceiptPromotionExternalObligation.OriginReceiptPromotionEvidence"
    ; exactPromotedStatusReceiptName =
        "DASHI.Physics.Closure.OriginReceiptPromotionExternalObligation.PromotedOriginEmpiricalStatusReceipt"
    ; exactAuthorityTokenName =
        "DASHI.Physics.Closure.OriginReceiptPromotionExternalObligation.ExternalOriginPromotedEmpiricalStatusAuthority"
    ; exactBlockedReceiptFields =
        "empiricalPromotionEvidence : OriginReceiptPromotionEvidence"
        ∷ "originObservationMap : MinimalCredibleShiftOriginCarrier -> MinimalCredibleShiftOriginObs"
        ∷ "originObservationMapCompatibility : originObservationMap agrees with originObservationMapMinimalCredibleShift"
        ∷ "closureBoundaryCarrier : Set"
        ∷ "closureBoundaryPreservation : MinimalCredibleShiftClosureBoundary -> closureBoundaryCarrier"
        ∷ "closureBoundaryReflectsCurrentReceipt : closureBoundaryCarrier -> current receipt closure boundary"
        ∷ "currentOriginReceiptStillBlocked : current receipt empiricalStatus == empiricalBlocked"
        ∷ []
    ; requiredProviderEvidence =
        "Either provide P0.EmpiricalAdequacy over the current MinimalCredibleShift origin carrier/observation pair"
        ∷ "or provide PromotedOriginEmpiricalStatusReceipt with ExternalOriginPromotedEmpiricalStatusAuthority"
        ∷ "provide an originObservationMap and compatibility proof against originObservationMapMinimalCredibleShift"
        ∷ "provide closure boundary carrier, preservation, and reflection into the current receipt boundary"
        ∷ "preserve the proof that the current MinimalCredibleShift origin receipt itself remains empiricalBlocked"
        ∷ []
    ; providerInstructions =
        "Use the exact W8 receipt type named above; do not replace it with a surrogate empirical surface"
        ∷ "The receipt must target the current MinimalCredibleShift origin receipt, not a broader physics-closure package"
        ∷ "If no positive receipt can be supplied, return a typed mismatch/authority diagnostic rather than prose"
        ∷ []
    ; sourceDiagnosticSummary =
        "canonicalCurrentOriginAuthoritySourceDiagnostic reports no current origin authority source"
        ∷ "current source scan requires ExternalOriginPromotedEmpiricalStatusAuthority or an origin-specific P0.EmpiricalAdequacy bridge"
        ∷ "the current MinimalCredibleShift origin receipt remains empiricalBlocked"
        ∷ []
    ; nonPromotionBoundary =
        "This pack is a request surface only"
        ∷ "It does not construct OriginReceiptPromotionExternalReceipt"
        ∷ "It does not construct ExternalOriginPromotedEmpiricalStatusAuthority"
        ∷ "It does not construct P0.EmpiricalAdequacy for the current origin receipt"
        ∷ "It does not promote W3, W8, origin empirical adequacy, or closure"
        ∷ []
    ; strictBlockerImpact =
        "W8 remains blocked until OriginReceiptPromotionExternalReceipt is externally supplied"
        ∷ "W3 Option C real-dataset authority remains blocked on the W8 origin-promotion receipt"
        ∷ "This module only makes the W8 provider handoff typed and auditable"
        ∷ []
    }

canonicalOriginReceiptPromotionExternalRequestPackStatus :
  OriginReceiptPromotionExternalRequestPackStatus
canonicalOriginReceiptPromotionExternalRequestPackStatus =
  blockedAwaitingExternalOriginPromotionReceipt
