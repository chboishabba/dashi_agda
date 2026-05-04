module DASHI.Interop.PNFResidualConsumerRuntimeProviderAttempt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Interop.PNFResidualConsumerNextObligation as W6
import DASHI.Interop.PNFResidualConsumerReceiptRequestPack as Request
import Ontology.Hecke.PNFResidualBridge as Hecke

------------------------------------------------------------------------
-- W6 runtime provider attempt.
--
-- The local repo currently exposes the constructor and builder surfaces, but
-- no concrete runtime payload values.  This module is therefore a typed
-- diagnostic, not a positive fixture: it does not manufacture PNF emissions,
-- consumer ids, or Hecke candidate-pool receipt ids.

data PNFResidualConsumerRuntimeProviderConclusion : Set where
  diagnosticOnlyMissingRuntimePayload :
    PNFResidualConsumerRuntimeProviderConclusion

record PNFResidualConsumerRuntimeProviderAttempt : Setω where
  field
    conclusion :
      PNFResidualConsumerRuntimeProviderConclusion

    requestPack :
      Request.PNFResidualConsumerReceiptRequestPack

    existingRuntimeSurfaces :
      List W6.PNFResidualConsumerExistingRuntimeSource

    absentRuntimePayloadFields :
      List W6.PNFResidualConsumerMissingRuntimeSource

    requiredRuntimePayloadFields :
      List W6.PNFResidualConsumerRuntimeSuppliedField

    derivableAfterRuntimePayload :
      List W6.PNFResidualConsumerDerivedReceiptField

    nonInspectionBoundaries :
      List W6.PNFResidualConsumerNonInspectionBoundary

    heckeCandidatePoolBoundary :
      List String

    payloadBuilderIfSupplied :
      Request.PNFResidualConsumerRuntimeReceiptPayload →
      W6.PNFResidualConsumerReceipt

    noSyntheticPromotionBoundary :
      List String

canonicalMissingRuntimePayloadFields :
  List W6.PNFResidualConsumerMissingRuntimeSource
canonicalMissingRuntimePayloadFields =
  W6.missingConcreteConsumerProfileValue
  ∷ W6.missingConcreteRuntimeReceiptIdValue
  ∷ W6.missingConcreteLeftPNFEmissionReceiptValue
  ∷ W6.missingConcreteRightPNFEmissionReceiptValue
  ∷ W6.missingConcreteReceiptBackedResidualComputation
  ∷ W6.missingConcreteHeckeCandidatePoolReceiptIdValue
  ∷ []

canonicalMissingRuntimePayloadFieldsComplete :
  canonicalMissingRuntimePayloadFields
  ≡
  W6.canonicalPNFResidualConsumerMissingRuntimeSources
canonicalMissingRuntimePayloadFieldsComplete = refl

canonicalRuntimeProviderAttempt :
  PNFResidualConsumerRuntimeProviderAttempt
canonicalRuntimeProviderAttempt =
  record
    { conclusion =
        diagnosticOnlyMissingRuntimePayload
    ; requestPack =
        Request.canonicalPNFResidualConsumerReceiptRequestPack
    ; existingRuntimeSurfaces =
        W6.PNFResidualConsumerRuntimeReceiptSourceDiagnostic.existingRuntimeSources
          W6.canonicalPNFResidualConsumerRuntimeReceiptSourceDiagnostic
    ; absentRuntimePayloadFields =
        canonicalMissingRuntimePayloadFields
    ; requiredRuntimePayloadFields =
        Request.canonicalRequestPackRequiredFields
    ; derivableAfterRuntimePayload =
        W6.canonicalPNFResidualConsumerDerivableFields
    ; nonInspectionBoundaries =
        W6.PNFResidualConsumerMissingReceiptDiagnostic.nonInspectionBoundaries
          W6.canonicalPNFResidualConsumerMissingReceiptDiagnostic
    ; heckeCandidatePoolBoundary =
        Hecke.HeckePNFResidualBridgeSurface.nonClaimBoundary
          Hecke.heckePNFResidualBridgeSurface
    ; payloadBuilderIfSupplied =
        Request.payloadToConsumerReceipt
    ; noSyntheticPromotionBoundary =
        "No positive PNFResidualConsumerReceipt fixture is exported because no concrete runtime payload is present"
        ∷ "The absent payload fields are exactly: consumer profile, runtime receipt id, left PNFEmissionReceipt, right PNFEmissionReceipt, receipt-backed residual computation, and Hecke candidate-pool receipt id"
        ∷ "If runtime supplies those fields, Request.payloadToConsumerReceipt constructs the consumer receipt with atom and residual projections by refl"
        ∷ "This attempt does not synthesize atom labels, wrapper labels, qualifier labels, role bindings, residual levels, or Hecke fibre labels"
        ∷ []
    }

runtimeProviderAttemptMissingFields :
  List W6.PNFResidualConsumerMissingRuntimeSource
runtimeProviderAttemptMissingFields =
  PNFResidualConsumerRuntimeProviderAttempt.absentRuntimePayloadFields
    canonicalRuntimeProviderAttempt

runtimeProviderAttemptMissingFieldsComplete :
  runtimeProviderAttemptMissingFields
  ≡
  W6.canonicalPNFResidualConsumerMissingRuntimeSources
runtimeProviderAttemptMissingFieldsComplete = refl

runtimeProviderAttemptConclusionIsDiagnostic :
  PNFResidualConsumerRuntimeProviderAttempt.conclusion
    canonicalRuntimeProviderAttempt
  ≡
  diagnosticOnlyMissingRuntimePayload
runtimeProviderAttemptConclusionIsDiagnostic = refl

data PNFResidualConsumerRuntimeProviderOutput : Setω where
  runtimePayloadPresent :
    Request.PNFResidualConsumerRuntimeReceiptPayload →
    PNFResidualConsumerRuntimeProviderOutput
  runtimePayloadAbsentDiagnostic :
    PNFResidualConsumerRuntimeProviderAttempt →
    PNFResidualConsumerRuntimeProviderOutput

canonicalRuntimeProviderOutput :
  PNFResidualConsumerRuntimeProviderOutput
canonicalRuntimeProviderOutput =
  runtimePayloadAbsentDiagnostic canonicalRuntimeProviderAttempt
