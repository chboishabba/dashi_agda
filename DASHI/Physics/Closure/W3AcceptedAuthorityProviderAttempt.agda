module DASHI.Physics.Closure.W3AcceptedAuthorityProviderAttempt where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.HEPDataResidualObservableClassReceiptProtoAlignment as Residual
import DASHI.Physics.Closure.HEPDataW3ComparisonLawReceipt as Comparison
import DASHI.Physics.Closure.HEPDataW3NonCollapseWitnessReceipt as NonCollapse
import DASHI.Physics.Closure.HEPDataW3PromotionCandidate as Candidate
import DASHI.Physics.Closure.OriginReceiptPromotionExternalObligation as W8
import DASHI.Physics.Closure.OriginReceiptPromotionExternalRequestPack as W8Pack
import DASHI.Physics.Closure.W3AcceptedAuthorityExternalReceiptObligation as EXT
import DASHI.Physics.Closure.W3AcceptedAuthorityExternalReceiptRequestPack as Pack
import DASHI.Physics.Closure.W3AcceptedAuthorityRouteNarrowing as Route
import DASHI.Physics.Closure.W3AcceptedEmpiricalAuthorityGate as AUTH
import DASHI.Physics.Closure.W3EmpiricalTargetPromotionBridgeObligation as W3

------------------------------------------------------------------------
-- W3 provider attempt / source diagnostic.
--
-- This module owns only the provider-attempt result for the current W3
-- accepted-authority lane.  It does not construct accepted empirical
-- authority, B4 empirical promotion, origin promotion, or an external receipt.

data W3AcceptedAuthorityProviderAttemptDecision : Set where
  noLocalAcceptedAuthorityExternalReceipt :
    W3AcceptedAuthorityProviderAttemptDecision

data W3AcceptedAuthorityProviderSourcePresence : Set where
  sourceMissing :
    W3AcceptedAuthorityProviderSourcePresence

data W3AcceptedAuthorityProviderAttemptBlocker : Set where
  acceptedEvidenceAuthorityTokenMissing :
    W3AcceptedAuthorityProviderAttemptBlocker
  evidenceBackedEmpiricalTargetMissing :
    W3AcceptedAuthorityProviderAttemptBlocker
  evidenceAuthorityEqualityMissing :
    W3AcceptedAuthorityProviderAttemptBlocker
  b4EmpiricalPromotionMissing :
    W3AcceptedAuthorityProviderAttemptBlocker
  originReceiptPromotionMissing :
    W3AcceptedAuthorityProviderAttemptBlocker
  bridgeObligationsMissing :
    W3AcceptedAuthorityProviderAttemptBlocker
  bridgeTargetEvidenceEqualityMissing :
    W3AcceptedAuthorityProviderAttemptBlocker
  w8OriginPromotionExternalReceiptMissing :
    W3AcceptedAuthorityProviderAttemptBlocker

data W3AcceptedAuthorityProviderAttemptClosureToken : Set where

canonicalW3AcceptedAuthorityProviderAttemptBlockers :
  List W3AcceptedAuthorityProviderAttemptBlocker
canonicalW3AcceptedAuthorityProviderAttemptBlockers =
  acceptedEvidenceAuthorityTokenMissing
  ∷ evidenceBackedEmpiricalTargetMissing
  ∷ evidenceAuthorityEqualityMissing
  ∷ b4EmpiricalPromotionMissing
  ∷ originReceiptPromotionMissing
  ∷ bridgeObligationsMissing
  ∷ bridgeTargetEvidenceEqualityMissing
  ∷ w8OriginPromotionExternalReceiptMissing
  ∷ []

record W3AcceptedAuthorityProviderAttemptDiagnostic : Setω where
  field
    requestPack :
      Pack.W3AcceptedAuthorityExternalReceiptRequestPack

    providerPayloadRequest :
      Pack.W3AcceptedAuthorityProviderPayloadRequest

    currentExternalStatus :
      EXT.W3AcceptedAuthorityExternalReceiptCurrentStatus

    routeDiagnostic :
      Route.W3AcceptedAuthorityRouteCurrentDiagnostic

    bridgeObligationReceipt :
      W3.W3EmpiricalTargetPromotionBridgeObligationReceipt

    originPromotionRequestPack :
      W8Pack.OriginReceiptPromotionExternalRequestPack

    originPromotionCurrentStatus :
      W8.OriginReceiptPromotionExternalCurrentStatus

    w3PromotionCandidate :
      Candidate.HEPDataW3PromotionCandidate

    w3ComparisonLawReceipt :
      Comparison.W3ComparisonLawReceipt

    w3RunnerPerBinNonCollapseReceipt :
      NonCollapse.HEPDataW3T43RunnerPerBinNonCollapseReceipt

    residualProtoAlignment :
      Residual.HEPDataResidualObservableClassReceiptProtoAlignment

    constructionDecision :
      W3AcceptedAuthorityProviderAttemptDecision

    externalReceiptSource :
      W3AcceptedAuthorityProviderSourcePresence

    authorityTokenSource :
      W3AcceptedAuthorityProviderSourcePresence

    evidenceBackedTargetSource :
      W3AcceptedAuthorityProviderSourcePresence

    b4PromotionSource :
      W3AcceptedAuthorityProviderSourcePresence

    originPromotionSource :
      W3AcceptedAuthorityProviderSourcePresence

    bridgeObligationsSource :
      W3AcceptedAuthorityProviderSourcePresence

    providerMissingFields :
      List Pack.W3AcceptedAuthorityProviderMissingField

    providerMissingFieldsAreCanonical :
      providerMissingFields
      ≡
      Pack.W3AcceptedAuthorityProviderPayloadRequest.missingProviderFields
        Pack.canonicalW3AcceptedAuthorityProviderPayloadRequest

    firstMissingAuthorityProviderField :
      Pack.W3AcceptedAuthorityProviderMissingField

    firstMissingAuthorityProviderFieldIsAcceptedEvidenceAuthorityToken :
      firstMissingAuthorityProviderField
      ≡
      Pack.missingAcceptedEvidenceAuthorityToken

    attemptBlockers :
      List W3AcceptedAuthorityProviderAttemptBlocker

    attemptBlockersAreCanonical :
      attemptBlockers
      ≡
      canonicalW3AcceptedAuthorityProviderAttemptBlockers

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

    authorityGateStatuses :
      List AUTH.W3AuthorityGateStatus

    authorityGateStatusesAreCanonical :
      authorityGateStatuses
      ≡
      AUTH.canonicalCurrentW3AcceptedAuthorityStatuses

    externalReceiptStatuses :
      List EXT.W3AcceptedAuthorityExternalReceiptStatus

    externalReceiptStatusesAreCanonical :
      externalReceiptStatuses
      ≡
      EXT.canonicalW3AcceptedAuthorityExternalReceiptStatuses

    w8BlockedFields :
      List W8.OriginReceiptPromotionExternalBlockedField

    w8BlockedFieldsAreCanonical :
      w8BlockedFields
      ≡
      W8.canonicalOriginReceiptPromotionExternalBlockedFields

    w8SourceScanResult :
      W8.OriginEmpiricalAuthoritySourceScanResult

    w8SourceScanResultIsCanonical :
      w8SourceScanResult
      ≡
      W8.noCurrentOriginAuthoritySourceFound

    r51CandidateNumericPasses :
      Candidate.HEPDataW3PromotionCandidate.cleanRunNumericPass
        w3PromotionCandidate
      ≡
      true

    r52ComparisonLawPromotesBoundedT43 :
      Comparison.W3ComparisonLawReceipt.w3Status w3ComparisonLawReceipt
      ≡
      Comparison.promotedT43BelowZOnly

    r53RunnerPerBinWitnessExtracted :
      NonCollapse.HEPDataW3T43RunnerPerBinNonCollapseReceipt.status
        w3RunnerPerBinNonCollapseReceipt
      ≡
      NonCollapse.perBinRunnerWitnessExtracted

    r53AuthorityTokenConstructedHereIsFalse :
      NonCollapse.HEPDataW3T43RunnerPerBinNonCollapseReceipt.authorityTokenConstructedHere
        w3RunnerPerBinNonCollapseReceipt
      ≡
      false

    r53ExternalReceiptConstructedHereIsFalse :
      NonCollapse.HEPDataW3T43RunnerPerBinNonCollapseReceipt.acceptedAuthorityExternalReceiptConstructedHere
        w3RunnerPerBinNonCollapseReceipt
      ≡
      false

    impossibleAuthorityHere :
      AUTH.W3AcceptedEvidenceAuthorityToken →
      EXT.W3AcceptedAuthorityExternalReceiptImpossible

    impossibleEvidenceTargetHere :
      AUTH.W3EvidenceBackedEmpiricalTarget →
      EXT.W3AcceptedAuthorityExternalReceiptImpossible

    impossibleExternalReceiptHere :
      EXT.W3AcceptedAuthorityExternalReceipt →
      EXT.W3AcceptedAuthorityExternalReceiptImpossible

    closureWouldNeedExternalReceipt :
      W3AcceptedAuthorityProviderAttemptClosureToken →
      EXT.W3AcceptedAuthorityExternalReceipt

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

    exactW8ExternalReceiptName :
      String

    nextProviderPacket :
      String

    diagnosticBoundary :
      List String

    blockerImpact :
      List String

canonicalW3AcceptedAuthorityProviderAttemptDiagnostic :
  W3AcceptedAuthorityProviderAttemptDiagnostic
canonicalW3AcceptedAuthorityProviderAttemptDiagnostic =
  record
    { requestPack =
        Pack.canonicalW3AcceptedAuthorityExternalReceiptRequestPack
    ; providerPayloadRequest =
        Pack.canonicalW3AcceptedAuthorityProviderPayloadRequest
    ; currentExternalStatus =
        EXT.currentW3AcceptedAuthorityExternalReceiptStatus
    ; routeDiagnostic =
        Route.canonicalW3AcceptedAuthorityRouteCurrentDiagnostic
    ; bridgeObligationReceipt =
        W3.canonicalW3EmpiricalTargetPromotionBridgeObligationReceipt
    ; originPromotionRequestPack =
        W8Pack.canonicalOriginReceiptPromotionExternalRequestPack
    ; originPromotionCurrentStatus =
        W8.canonicalOriginReceiptPromotionExternalCurrentStatus
    ; w3PromotionCandidate =
        Candidate.canonicalHEPDataW3PromotionCandidate
    ; w3ComparisonLawReceipt =
        Comparison.canonicalHEPDataW3ComparisonLawReceipt
    ; w3RunnerPerBinNonCollapseReceipt =
        NonCollapse.canonicalHEPDataW3T43RunnerPerBinNonCollapseReceipt
    ; residualProtoAlignment =
        Residual.canonicalHEPDataResidualObservableClassReceiptProtoAlignment
    ; constructionDecision =
        noLocalAcceptedAuthorityExternalReceipt
    ; externalReceiptSource =
        sourceMissing
    ; authorityTokenSource =
        sourceMissing
    ; evidenceBackedTargetSource =
        sourceMissing
    ; b4PromotionSource =
        sourceMissing
    ; originPromotionSource =
        sourceMissing
    ; bridgeObligationsSource =
        sourceMissing
    ; providerMissingFields =
        Pack.W3AcceptedAuthorityProviderPayloadRequest.missingProviderFields
          Pack.canonicalW3AcceptedAuthorityProviderPayloadRequest
    ; providerMissingFieldsAreCanonical =
        refl
    ; firstMissingAuthorityProviderField =
        Pack.missingAcceptedEvidenceAuthorityToken
    ; firstMissingAuthorityProviderFieldIsAcceptedEvidenceAuthorityToken =
        refl
    ; attemptBlockers =
        canonicalW3AcceptedAuthorityProviderAttemptBlockers
    ; attemptBlockersAreCanonical =
        refl
    ; routeBlockers =
        Route.canonicalW3AcceptedAuthorityRouteBlockers
    ; routeBlockersAreCanonical =
        refl
    ; routeBlockersAreCurrent =
        refl
    ; authorityGateStatuses =
        AUTH.canonicalCurrentW3AcceptedAuthorityStatuses
    ; authorityGateStatusesAreCanonical =
        refl
    ; externalReceiptStatuses =
        EXT.canonicalW3AcceptedAuthorityExternalReceiptStatuses
    ; externalReceiptStatusesAreCanonical =
        refl
    ; w8BlockedFields =
        W8.canonicalOriginReceiptPromotionExternalBlockedFields
    ; w8BlockedFieldsAreCanonical =
        refl
    ; w8SourceScanResult =
        W8.noCurrentOriginAuthoritySourceFound
    ; w8SourceScanResultIsCanonical =
        refl
    ; r51CandidateNumericPasses =
        refl
    ; r52ComparisonLawPromotesBoundedT43 =
        refl
    ; r53RunnerPerBinWitnessExtracted =
        refl
    ; r53AuthorityTokenConstructedHereIsFalse =
        refl
    ; r53ExternalReceiptConstructedHereIsFalse =
        refl
    ; impossibleAuthorityHere =
        Pack.W3AcceptedAuthorityProviderPayloadRequest.impossibleAuthorityHere
          Pack.canonicalW3AcceptedAuthorityProviderPayloadRequest
    ; impossibleEvidenceTargetHere =
        Pack.W3AcceptedAuthorityProviderPayloadRequest.impossibleEvidenceTargetHere
          Pack.canonicalW3AcceptedAuthorityProviderPayloadRequest
    ; impossibleExternalReceiptHere =
        Pack.W3AcceptedAuthorityProviderPayloadRequest.impossibleExternalReceiptHere
          Pack.canonicalW3AcceptedAuthorityProviderPayloadRequest
    ; closureWouldNeedExternalReceipt =
        λ ()
    ; exactExternalReceiptName =
        Pack.W3AcceptedAuthorityProviderPayloadRequest.exactExternalReceiptName
          Pack.canonicalW3AcceptedAuthorityProviderPayloadRequest
    ; exactAuthorityTokenName =
        Pack.W3AcceptedAuthorityProviderPayloadRequest.exactAuthorityTokenName
          Pack.canonicalW3AcceptedAuthorityProviderPayloadRequest
    ; exactEvidenceBackedTargetName =
        Pack.W3AcceptedAuthorityProviderPayloadRequest.exactEvidenceBackedTargetName
          Pack.canonicalW3AcceptedAuthorityProviderPayloadRequest
    ; exactB4PromotionName =
        Pack.W3AcceptedAuthorityProviderPayloadRequest.exactB4PromotionName
          Pack.canonicalW3AcceptedAuthorityProviderPayloadRequest
    ; exactOriginPromotionName =
        Pack.W3AcceptedAuthorityProviderPayloadRequest.exactOriginPromotionName
          Pack.canonicalW3AcceptedAuthorityProviderPayloadRequest
    ; exactBridgeObligationsName =
        Pack.W3AcceptedAuthorityProviderPayloadRequest.exactBridgeObligationsName
          Pack.canonicalW3AcceptedAuthorityProviderPayloadRequest
    ; exactW8ExternalReceiptName =
        W8Pack.OriginReceiptPromotionExternalRequestPack.exactExternalReceiptName
          W8Pack.canonicalOriginReceiptPromotionExternalRequestPack
    ; nextProviderPacket =
        Pack.W3AcceptedAuthorityProviderPayloadRequest.exactAuthorityTokenName
          Pack.canonicalW3AcceptedAuthorityProviderPayloadRequest
    ; diagnosticBoundary =
        "HEP-R51/R52/R53 surfaces are consumed: bounded t43 candidate, comparison-law receipt, and runner per-bin non-collapse receipt"
        ∷ "No legitimate W3AcceptedAuthorityExternalReceipt is locally constructible from current repo artifacts"
        ∷ "The first missing field is W3AcceptedEvidenceAuthorityToken, which is constructorless and is not supplied by the request pack"
        ∷ "Any evidence-backed empirical target or accepted-authority external receipt eliminates through that missing authority token"
        ∷ "B4 empirical promotion remains missing because the current B4 shell report is standaloneOnly"
        ∷ "Origin promotion remains missing because W8 reports no current origin authority source and the current origin receipt remains empiricalBlocked"
        ∷ "Standalone empirical packaging is preserved as non-authority evidence only"
        ∷ []
    ; blockerImpact =
        "Positive receipt unavailable: W3 remains blocked on accepted authority, evidence-backed target, B4 promotion, origin promotion, and bridge equalities"
        ∷ "The admissible output of this lane is this typed provider-attempt diagnostic"
        ∷ "W0 may wire this diagnostic as a W3 provider-attempt result without treating it as promotion"
        ∷ []
    }

canonicalW3AcceptedAuthorityProviderAttemptDecision :
  W3AcceptedAuthorityProviderAttemptDecision
canonicalW3AcceptedAuthorityProviderAttemptDecision =
  W3AcceptedAuthorityProviderAttemptDiagnostic.constructionDecision
    canonicalW3AcceptedAuthorityProviderAttemptDiagnostic
