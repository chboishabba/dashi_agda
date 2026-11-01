module DASHI.Physics.Closure.GRQFTClosurePromotionReceiptRequestPack where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.GRQFTConsumerNextObligation as W5
import DASHI.Physics.Closure.GRQFTConsumerNextObligationV2 as W5V2
import DASHI.Physics.Closure.GRQFTConsumerSourceDiagnostic as W5Source

------------------------------------------------------------------------
-- W5h GR/QFT closure-promotion receipt request pack.
--
-- This module packages the missing provider-facing inputs for W5.  It does
-- not construct promotion authority, GR/QFT laws, consumer witnesses,
-- empirical validation, downstream fields, or a closure-promotion receipt.

data GRQFTClosurePromotionRequestPackStatus : Set where
  blockedAwaitingGRQFTClosurePromotionReceipt :
    GRQFTClosurePromotionRequestPackStatus

record GRQFTClosurePromotionProviderPayloadRequest : Setω where
  field
    sourceDiagnostic :
      W5Source.GRQFTConsumerSourceDiagnostic

    exactReceiptName :
      String

    exactMissingReceiptFields :
      List String

    missingUpstreamFields :
      List W5.GRQFTConsumerMissingUpstreamField

    firstMissingPolicy :
      List W5.GRQFTConsumerFirstMissingReceipt

    firstMissingPolicyStillCanonical :
      firstMissingPolicy
      ≡
      W5.canonicalGRQFTConsumerFirstMissingPolicy

    exactFirstMissingName :
      String

    limitedPromotionGateName :
      String

    missingUpstreamFieldsStillCanonical :
      missingUpstreamFields
      ≡
      W5.canonicalGRQFTConsumerBlockedFields

    missingFieldsReceipt :
      W5.GRQFTClosurePromotionReceiptMissingFields

    pdfCarrierPrerequisite :
      W5.GRQFTPDFCarrierPrerequisiteDiagnostic

    missingFieldsReceiptStillCanonical :
      missingFieldsReceipt
      ≡
      W5.canonicalGRQFTConsumerReceiptMissingFields

    sourceAvailability :
      W5Source.GRQFTConsumerReceiptSourceAvailability

    partialConsumerReceipt :
      W5V2.GRQFTPartialConsumerReceipt

    sourceAvailabilityStillDiagnosticCanonical :
      sourceAvailability
      ≡
      W5Source.canonicalGRQFTConsumerReceiptSourceAvailability

    providerInstructions :
      List String

    nonPromotionBoundary :
      List String

    strictBlockerImpact :
      List String

    impossibleAuthorityHere :
      W5.GRQFTClosurePromotionAuthorityToken →
      ⊥

    impossibleReceiptHere :
      W5.GRQFTClosurePromotionReceipt →
      ⊥

    impossibleLimitedPromotionGateHere :
      W5.LimitedSMQFTGRPromotionPrerequisiteGate →
      ⊥

canonicalGRQFTClosurePromotionProviderPayloadRequest :
  GRQFTClosurePromotionProviderPayloadRequest
canonicalGRQFTClosurePromotionProviderPayloadRequest =
  record
    { sourceDiagnostic =
        W5Source.canonicalGRQFTConsumerSourceDiagnostic
    ; exactReceiptName =
        "DASHI.Physics.Closure.GRQFTConsumerNextObligation.GRQFTClosurePromotionReceipt"
    ; exactMissingReceiptFields =
        "promotionAuthority : GRQFTClosurePromotionAuthorityToken"
        ∷ "pdfCarrierPrerequisite : external PDF carrier/mass-kernel route before W5 GR/QFT/PDF closure intake"
        ∷ "downstreamConsumerFields : GRQFTDownstreamConsumerFields"
        ∷ "grEquationLaw : einsteinEquationCarrier -> Set"
        ∷ "qftInteractionLaw : interactionClosureCarrier -> Set"
        ∷ "grEquationLawAtConsumer : stressEnergy -> curvature -> grEquationLaw (einsteinEquationConsumer stressEnergy curvature)"
        ∷ "qftInteractionLawAtConsumer : waveState -> qftInteractionLaw (interactionClosureConsumer (gaugeRepresentationMap (spinorRealizationMap waveState)))"
        ∷ "empiricalGRQFTValidationReceipt : EmpiricalGRQFTValidationReceipt downstreamConsumerFields grEquationLaw qftInteractionLaw"
        ∷ "GRQFTClosurePromotionReceipt : required before LimitedSMQFTGRPromotionPrerequisiteGate or any limited SM/QFT+GR promotion"
        ∷ "empirical GR/QFT validation external to known-limits local recovery"
        ∷ []
    ; missingUpstreamFields =
        W5Source.GRQFTConsumerSourceDiagnostic.receiptBlockedFields
          W5Source.canonicalGRQFTConsumerSourceDiagnostic
    ; firstMissingPolicy =
        W5Source.GRQFTConsumerSourceDiagnostic.firstMissingPolicy
          W5Source.canonicalGRQFTConsumerSourceDiagnostic
    ; firstMissingPolicyStillCanonical =
        refl
    ; exactFirstMissingName =
        W5Source.GRQFTConsumerSourceDiagnostic.exactFirstMissingName
          W5Source.canonicalGRQFTConsumerSourceDiagnostic
    ; limitedPromotionGateName =
        W5Source.GRQFTConsumerSourceDiagnostic.limitedPromotionGateName
          W5Source.canonicalGRQFTConsumerSourceDiagnostic
    ; missingUpstreamFieldsStillCanonical =
        refl
    ; missingFieldsReceipt =
        W5Source.GRQFTConsumerSourceDiagnostic.receiptMissingFields
          W5Source.canonicalGRQFTConsumerSourceDiagnostic
    ; pdfCarrierPrerequisite =
        W5Source.GRQFTConsumerSourceDiagnostic.pdfCarrierPrerequisite
          W5Source.canonicalGRQFTConsumerSourceDiagnostic
    ; missingFieldsReceiptStillCanonical =
        refl
    ; sourceAvailability =
        W5Source.GRQFTConsumerSourceDiagnostic.sourceAvailability
          W5Source.canonicalGRQFTConsumerSourceDiagnostic
    ; partialConsumerReceipt =
        W5V2.canonicalGRQFTPartialConsumerReceipt
    ; sourceAvailabilityStillDiagnosticCanonical =
        refl
    ; providerInstructions =
        "External provider must supply the full GRQFTClosurePromotionReceipt payload, not another known-limits theorem"
        ∷ "The payload must include promotion authority, the PDF carrier prerequisite, downstream consumer fields, GR equation law, QFT interaction law, both consumer law witnesses, and EmpiricalGRQFTValidationReceipt"
        ∷ "Known-limits observable, GR bridge, and QFT bridge sources may be reused only as inputs to downstreamConsumerFields"
        ∷ "The partial V2 consumer receipt already supplies spacetime, wave-state, spinor-adapter, and gauge-representation carrier fields; provider payload must supply the external-gated stress-energy, curvature/Einstein, interaction, authority, PDF, and validation fields"
        ∷ "The empirical receipt must validate the same qftInteractionLaw consumed by qftInteractionLawAtConsumer"
        ∷ "If the full chain cannot be supplied, return the earliest missing name from canonicalGRQFTConsumerFirstMissingPolicy"
        ∷ []
    ; nonPromotionBoundary =
        "This request pack does not construct GRQFTClosurePromotionAuthorityToken"
        ∷ "This request pack does not construct an external PDF carrier or mass-kernel route"
        ∷ "This request pack does not construct GRQFTDownstreamConsumerFields"
        ∷ "This request pack does not construct GR/QFT laws, consumer witnesses, EmpiricalGRQFTValidationReceipt, or GRQFTClosurePromotionReceipt"
        ∷ "This request pack does not construct LimitedSMQFTGRPromotionPrerequisiteGate or any limited SM/QFT+GR promotion"
        ∷ []
    ; strictBlockerImpact =
        W5Source.GRQFTConsumerSourceDiagnostic.blockerImpact
          W5Source.canonicalGRQFTConsumerSourceDiagnostic
    ; impossibleAuthorityHere =
        W5Source.GRQFTConsumerSourceDiagnostic.impossibleAuthorityHere
          W5Source.canonicalGRQFTConsumerSourceDiagnostic
    ; impossibleReceiptHere =
        W5Source.GRQFTConsumerSourceDiagnostic.impossibleReceiptHere
          W5Source.canonicalGRQFTConsumerSourceDiagnostic
    ; impossibleLimitedPromotionGateHere =
        W5Source.GRQFTConsumerSourceDiagnostic.impossibleLimitedPromotionGateHere
          W5Source.canonicalGRQFTConsumerSourceDiagnostic
    }

record GRQFTClosurePromotionReceiptRequestPack : Setω where
  field
    currentStatus :
      GRQFTClosurePromotionRequestPackStatus

    sourceDiagnostic :
      W5Source.GRQFTConsumerSourceDiagnostic

    providerPayloadRequest :
      GRQFTClosurePromotionProviderPayloadRequest

    firstMissingPolicy :
      List W5.GRQFTConsumerFirstMissingReceipt

    exactFirstMissingName :
      String

    limitedPromotionGateName :
      String

    requiredNextReceipt :
      String

    knownLimitsBoundary :
      String

    partialConsumerReceipt :
      W5V2.GRQFTPartialConsumerReceipt

    closurePromotionBoundary :
      String

    consolidatedRequestBoundary :
      List String

    consolidatedStrictBlockerImpact :
      List String

canonicalGRQFTClosurePromotionReceiptRequestPack :
  GRQFTClosurePromotionReceiptRequestPack
canonicalGRQFTClosurePromotionReceiptRequestPack =
  record
    { currentStatus =
        blockedAwaitingGRQFTClosurePromotionReceipt
    ; sourceDiagnostic =
        W5Source.canonicalGRQFTConsumerSourceDiagnostic
    ; providerPayloadRequest =
        canonicalGRQFTClosurePromotionProviderPayloadRequest
    ; firstMissingPolicy =
        GRQFTClosurePromotionProviderPayloadRequest.firstMissingPolicy
          canonicalGRQFTClosurePromotionProviderPayloadRequest
    ; exactFirstMissingName =
        GRQFTClosurePromotionProviderPayloadRequest.exactFirstMissingName
          canonicalGRQFTClosurePromotionProviderPayloadRequest
    ; limitedPromotionGateName =
        GRQFTClosurePromotionProviderPayloadRequest.limitedPromotionGateName
          canonicalGRQFTClosurePromotionProviderPayloadRequest
    ; requiredNextReceipt =
        W5Source.GRQFTConsumerSourceDiagnostic.requiredNextReceipt
          W5Source.canonicalGRQFTConsumerSourceDiagnostic
    ; knownLimitsBoundary =
        W5Source.GRQFTConsumerSourceDiagnostic.knownLimitsBoundary
          W5Source.canonicalGRQFTConsumerSourceDiagnostic
    ; partialConsumerReceipt =
        W5V2.canonicalGRQFTPartialConsumerReceipt
    ; closurePromotionBoundary =
        W5Source.GRQFTConsumerSourceDiagnostic.closurePromotionBoundary
          W5Source.canonicalGRQFTConsumerSourceDiagnostic
    ; consolidatedRequestBoundary =
        "Request pack only aggregates W5 and W5g diagnostics into provider-facing missing receipt fields"
        ∷ "It adds the PDF carrier prerequisite as a diagnostic field, not as a supplied carrier"
        ∷ "It records the V2 partial consumer receipt for internally adaptable carriers only"
        ∷ "It does not promote known-limits GR/QFT bridge results into full GR/QFT closure"
        ∷ "It does not discharge W5, empirical validation, or downstream physics authority blockers"
        ∷ "It requires qftInteractionLaw, qftInteractionLawAtConsumer, EmpiricalGRQFTValidationReceipt, and GRQFTClosurePromotionReceipt authority before any limited SM/QFT+GR promotion"
        ∷ []
    ; consolidatedStrictBlockerImpact =
        "W5 remains blocked until an external GRQFTClosurePromotionReceipt is supplied"
        ∷ "Constructorless local promotion authority keeps closure promotion impossible in this module"
        ∷ "Next admissible worker target is provider construction of the named receipt payload or an explicit theorem-route change"
        ∷ []
    }
