module DASHI.Physics.Closure.GRQFTClosurePromotionReceiptRequestPack where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.GRQFTConsumerNextObligation as W5
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

    missingUpstreamFieldsStillCanonical :
      missingUpstreamFields
      ≡
      W5.canonicalGRQFTConsumerBlockedFields

    missingFieldsReceipt :
      W5.GRQFTClosurePromotionReceiptMissingFields

    missingFieldsReceiptStillCanonical :
      missingFieldsReceipt
      ≡
      W5.canonicalGRQFTConsumerReceiptMissingFields

    sourceAvailability :
      W5Source.GRQFTConsumerReceiptSourceAvailability

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
        ∷ "downstreamConsumerFields : GRQFTDownstreamConsumerFields"
        ∷ "grEquationLaw : einsteinEquationCarrier -> Set"
        ∷ "qftInteractionLaw : interactionClosureCarrier -> Set"
        ∷ "grEquationLawAtConsumer : stressEnergy -> curvature -> grEquationLaw (einsteinEquationConsumer stressEnergy curvature)"
        ∷ "qftInteractionLawAtConsumer : waveState -> qftInteractionLaw (interactionClosureConsumer (gaugeRepresentationMap (spinorRealizationMap waveState)))"
        ∷ "empirical GR/QFT validation external to known-limits local recovery"
        ∷ []
    ; missingUpstreamFields =
        W5Source.GRQFTConsumerSourceDiagnostic.receiptBlockedFields
          W5Source.canonicalGRQFTConsumerSourceDiagnostic
    ; missingUpstreamFieldsStillCanonical =
        refl
    ; missingFieldsReceipt =
        W5Source.GRQFTConsumerSourceDiagnostic.receiptMissingFields
          W5Source.canonicalGRQFTConsumerSourceDiagnostic
    ; missingFieldsReceiptStillCanonical =
        refl
    ; sourceAvailability =
        W5Source.GRQFTConsumerSourceDiagnostic.sourceAvailability
          W5Source.canonicalGRQFTConsumerSourceDiagnostic
    ; sourceAvailabilityStillDiagnosticCanonical =
        refl
    ; providerInstructions =
        "External provider must supply the full GRQFTClosurePromotionReceipt payload, not another known-limits theorem"
        ∷ "The payload must include promotion authority, downstream consumer fields, GR equation law, QFT interaction law, both consumer law witnesses, and empirical GR/QFT validation"
        ∷ "Known-limits observable, GR bridge, and QFT bridge sources may be reused only as inputs to downstreamConsumerFields"
        ∷ []
    ; nonPromotionBoundary =
        "This request pack does not construct GRQFTClosurePromotionAuthorityToken"
        ∷ "This request pack does not construct GRQFTDownstreamConsumerFields"
        ∷ "This request pack does not construct GR/QFT laws, consumer witnesses, empirical validation, or GRQFTClosurePromotionReceipt"
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
    }

record GRQFTClosurePromotionReceiptRequestPack : Setω where
  field
    currentStatus :
      GRQFTClosurePromotionRequestPackStatus

    sourceDiagnostic :
      W5Source.GRQFTConsumerSourceDiagnostic

    providerPayloadRequest :
      GRQFTClosurePromotionProviderPayloadRequest

    requiredNextReceipt :
      String

    knownLimitsBoundary :
      String

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
    ; requiredNextReceipt =
        W5Source.GRQFTConsumerSourceDiagnostic.requiredNextReceipt
          W5Source.canonicalGRQFTConsumerSourceDiagnostic
    ; knownLimitsBoundary =
        W5Source.GRQFTConsumerSourceDiagnostic.knownLimitsBoundary
          W5Source.canonicalGRQFTConsumerSourceDiagnostic
    ; closurePromotionBoundary =
        W5Source.GRQFTConsumerSourceDiagnostic.closurePromotionBoundary
          W5Source.canonicalGRQFTConsumerSourceDiagnostic
    ; consolidatedRequestBoundary =
        "Request pack only aggregates W5 and W5g diagnostics into provider-facing missing receipt fields"
        ∷ "It does not promote known-limits GR/QFT bridge results into full GR/QFT closure"
        ∷ "It does not discharge W5, empirical validation, or downstream physics authority blockers"
        ∷ []
    ; consolidatedStrictBlockerImpact =
        "W5 remains blocked until an external GRQFTClosurePromotionReceipt is supplied"
        ∷ "Constructorless local promotion authority keeps closure promotion impossible in this module"
        ∷ "Next admissible worker target is provider construction of the named receipt payload or an explicit theorem-route change"
        ∷ []
    }
