module DASHI.Physics.Closure.W3AcceptedEvidenceAuthorityTokenIntakeRequest where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.HEPDataW3NonCollapseWitnessReceipt as NonCollapse
import DASHI.Physics.Closure.W3AcceptedAuthorityExternalReceiptObligation as EXT
import DASHI.Physics.Closure.W3AcceptedAuthorityExternalReceiptRequestPack as Pack
import DASHI.Physics.Closure.W3AcceptedEmpiricalAuthorityGate as AUTH
import DASHI.Physics.Closure.W3T43AuthorityPacketCandidateDiagnostic as Candidate

------------------------------------------------------------------------
-- HEP-R55 token-only accepted-authority intake request.
--
-- The broader W3AcceptedAuthorityExternalReceiptRequestPack asks for the
-- complete accepted-authority receipt and its downstream bridge obligations.
-- This module narrows the first missing provider field to the authority token
-- itself.  It records the exact public/source and HEP-R53 runner evidence that
-- the provider token must acknowledge, while constructing no token locally.

data W3AcceptedEvidenceAuthorityTokenIntakeStatus : Set where
  blockedAwaitingExternalAcceptedEvidenceAuthorityToken :
    W3AcceptedEvidenceAuthorityTokenIntakeStatus

data W3AcceptedEvidenceAuthorityTokenFirstMissing : Set where
  firstMissingW3AcceptedEvidenceAuthorityToken :
    W3AcceptedEvidenceAuthorityTokenFirstMissing

data W3AuthorityTokenSelfIssuanceDecision : Set where
  selfIssuanceNotPermittedByConstructorlessGate :
    W3AuthorityTokenSelfIssuanceDecision

data W3AcceptedEvidenceAuthorityTokenPacketReadiness : Set where
  readyForExternalAuthorityTokenReview :
    W3AcceptedEvidenceAuthorityTokenPacketReadiness

data W3AcceptedEvidenceAuthorityTokenHandoffPacketStatus : Set where
  finalProviderFacingHandoffPacketRequestOnly :
    W3AcceptedEvidenceAuthorityTokenHandoffPacketStatus

record W3AcceptedEvidenceAuthorityTokenIntakeRequest : Setω where
  field
    status :
      W3AcceptedEvidenceAuthorityTokenIntakeStatus

    firstMissing :
      W3AcceptedEvidenceAuthorityTokenFirstMissing

    requestPack :
      Pack.W3AcceptedAuthorityExternalReceiptRequestPack

    providerPayloadRequest :
      Pack.W3AcceptedAuthorityProviderPayloadRequest

    currentExternalStatus :
      EXT.W3AcceptedAuthorityExternalReceiptCurrentStatus

    t43AuthorityPacket :
      Candidate.W3T43AuthorityPacketCandidateDiagnostic

    r53PerBinNonCollapseReceipt :
      NonCollapse.HEPDataW3T43RunnerPerBinNonCollapseReceipt

    packetReadiness :
      W3AcceptedEvidenceAuthorityTokenPacketReadiness

    handoffPacketStatus :
      W3AcceptedEvidenceAuthorityTokenHandoffPacketStatus

    packetReadyForExternalAuthority :
      Bool

    packetReadyForExternalAuthorityIsTrue :
      packetReadyForExternalAuthority
      ≡
      true

    witnessBinIndex :
      Float

    witnessBinIndexMatchesR53 :
      witnessBinIndex
      ≡
      NonCollapse.HEPDataW3T43RunnerPerBinNonCollapseReceipt.witnessBinIndex
        r53PerBinNonCollapseReceipt

    witnessPrediction :
      Float

    witnessPredictionMatchesR53 :
      witnessPrediction
      ≡
      NonCollapse.HEPDataW3T43RunnerPerBinNonCollapseReceipt.witnessPrediction
        r53PerBinNonCollapseReceipt

    witnessData :
      Float

    witnessDataMatchesR53 :
      witnessData
      ≡
      NonCollapse.HEPDataW3T43RunnerPerBinNonCollapseReceipt.witnessData
        r53PerBinNonCollapseReceipt

    witnessUncertainty :
      Float

    witnessUncertaintyMatchesR53 :
      witnessUncertainty
      ≡
      NonCollapse.HEPDataW3T43RunnerPerBinNonCollapseReceipt.witnessUncertainty
        r53PerBinNonCollapseReceipt

    witnessPull :
      Float

    witnessPullMatchesR53 :
      witnessPull
      ≡
      NonCollapse.HEPDataW3T43RunnerPerBinNonCollapseReceipt.witnessPull
        r53PerBinNonCollapseReceipt

    exactAuthorityTokenName :
      String

    exactAuthorityTokenNameMatchesPack :
      exactAuthorityTokenName
      ≡
      Pack.W3AcceptedAuthorityProviderPayloadRequest.exactAuthorityTokenName
        providerPayloadRequest

    exactFirstMissingProviderField :
      Pack.W3AcceptedAuthorityProviderMissingField

    exactFirstMissingProviderFieldIsToken :
      exactFirstMissingProviderField
      ≡
      Pack.missingAcceptedEvidenceAuthorityToken

    exactFirstMissingProviderFieldIsFirstInPack :
      Pack.W3AcceptedAuthorityProviderPayloadRequest.missingProviderFields
        providerPayloadRequest
      ≡
      Pack.missingAcceptedEvidenceAuthorityToken
      ∷
      Pack.missingEvidenceBackedEmpiricalTarget
      ∷
      Pack.missingEvidenceTargetAuthorityEquality
      ∷
      Pack.missingB4EmpiricalPromotion
      ∷
      Pack.missingOriginReceiptPromotion
      ∷
      Pack.missingBridgeObligations
      ∷
      Pack.missingBridgeTargetEvidenceEquality
      ∷
      []

    requiredTokenEvidenceFields :
      List String

    requiredTokenEvidenceFieldsArePublicAndRunnerBound :
      Bool

    requiredTokenEvidenceFieldsArePublicAndRunnerBoundIsTrue :
      requiredTokenEvidenceFieldsArePublicAndRunnerBound
      ≡
      true

    claimScopeBoundary :
      List String

    selfIssuanceDecision :
      W3AuthorityTokenSelfIssuanceDecision

    selfIssuancePermitted :
      Bool

    selfIssuancePermittedIsFalse :
      selfIssuancePermitted
      ≡
      false

    authorityTokenConstructedHere :
      Bool

    authorityTokenConstructedHereIsFalse :
      authorityTokenConstructedHere
      ≡
      false

    acceptedAuthorityExternalReceiptConstructedHere :
      Bool

    acceptedAuthorityExternalReceiptConstructedHereIsFalse :
      acceptedAuthorityExternalReceiptConstructedHere
      ≡
      false

    authorityTokenImpossibleHere :
      AUTH.W3AcceptedEvidenceAuthorityToken →
      EXT.W3AcceptedAuthorityExternalReceiptImpossible

    nonPromotionBoundary :
      List String

    providerTraceabilityChecklist :
      List String

    providerInstruction :
      List String

    providerFacingHandoffPacket :
      List String

    providerFacingHandoffPacketIsFinal :
      Bool

    providerFacingHandoffPacketIsFinalIsTrue :
      providerFacingHandoffPacketIsFinal
      ≡
      true

    exactFirstMissingBlocker :
      String

    exactFirstMissingStatus :
      String

    exactFirstMissingName :
      String

    exactFirstMissingNameMatchesAuthorityTokenName :
      exactFirstMissingName
      ≡
      exactAuthorityTokenName

    stillMissingPacketFields :
      List String

canonicalW3AcceptedEvidenceAuthorityTokenIntakeRequest :
  W3AcceptedEvidenceAuthorityTokenIntakeRequest
canonicalW3AcceptedEvidenceAuthorityTokenIntakeRequest =
  record
    { status =
        blockedAwaitingExternalAcceptedEvidenceAuthorityToken
    ; firstMissing =
        firstMissingW3AcceptedEvidenceAuthorityToken
    ; requestPack =
        Pack.canonicalW3AcceptedAuthorityExternalReceiptRequestPack
    ; providerPayloadRequest =
        Pack.canonicalW3AcceptedAuthorityProviderPayloadRequest
    ; currentExternalStatus =
        EXT.currentW3AcceptedAuthorityExternalReceiptStatus
    ; t43AuthorityPacket =
        Candidate.canonicalW3T43AuthorityPacketCandidateDiagnostic
    ; r53PerBinNonCollapseReceipt =
        NonCollapse.canonicalHEPDataW3T43RunnerPerBinNonCollapseReceipt
    ; packetReadiness =
        readyForExternalAuthorityTokenReview
    ; handoffPacketStatus =
        finalProviderFacingHandoffPacketRequestOnly
    ; packetReadyForExternalAuthority =
        true
    ; packetReadyForExternalAuthorityIsTrue =
        refl
    ; witnessBinIndex =
        12.0
    ; witnessBinIndexMatchesR53 =
        refl
    ; witnessPrediction =
        0.0486590199823977
    ; witnessPredictionMatchesR53 =
        refl
    ; witnessData =
        0.049758
    ; witnessDataMatchesR53 =
        refl
    ; witnessUncertainty =
        0.00048197510309143566
    ; witnessUncertaintyMatchesR53 =
        refl
    ; witnessPull =
        -2.280159308132989
    ; witnessPullMatchesR53 =
        refl
    ; exactAuthorityTokenName =
        Pack.W3AcceptedAuthorityProviderPayloadRequest.exactAuthorityTokenName
          Pack.canonicalW3AcceptedAuthorityProviderPayloadRequest
    ; exactAuthorityTokenNameMatchesPack =
        refl
    ; exactFirstMissingProviderField =
        Pack.missingAcceptedEvidenceAuthorityToken
    ; exactFirstMissingProviderFieldIsToken =
        refl
    ; exactFirstMissingProviderFieldIsFirstInPack =
        refl
    ; requiredTokenEvidenceFields =
        "datasetDOI: 10.17182/hepdata.104472"
        ∷ "paperDOI: 10.1140/epjc/s10052-023-11631-7"
        ∷ "submissionDOI: 10.17182/hepdata.115656.v1"
        ∷ "ratioTableDOI: 10.17182/hepdata.115656.v1/t43"
        ∷ "covarianceTableDOI: 10.17182/hepdata.115656.v1/t44"
        ∷ "observableConvention: UnnormalizedDifferentialCrossSectionRatio"
        ∷ "binCount: 18"
        ∷ "freezeCommit: 3205d746639568762c9e97adf4a3672c356bd491"
        ∷ "perBinArtifactSha256: 3987f82678943bab7679a9948e865f74f2263cdbe38a0e997734dad38939fda0"
        ∷ "perBinProjectionDigest: cc6ea1a8ea57ef376ae275c1b49e32b27d6d204d7b70cad5c6308b3f8a897a79"
        ∷ "nonCollapseWitness: bin 12, pred 0.0486590199823977, data 0.049758, unc 0.00048197510309143566, pull -2.280159308132989"
        ∷ []
    ; requiredTokenEvidenceFieldsArePublicAndRunnerBound =
        true
    ; requiredTokenEvidenceFieldsArePublicAndRunnerBoundIsTrue =
        refl
    ; claimScopeBoundary =
        "Claim scope is limited SM+GR empirical coordination for the bounded below-Z t43 lane"
        ∷ "This packet is not a broad unification claim"
        ∷ "This packet is not full Standard Model coverage"
        ∷ "This packet is not curved-GR closure, W4/W5 promotion, or W8 origin promotion"
        ∷ []
    ; selfIssuanceDecision =
        selfIssuanceNotPermittedByConstructorlessGate
    ; selfIssuancePermitted =
        false
    ; selfIssuancePermittedIsFalse =
        refl
    ; authorityTokenConstructedHere =
        false
    ; authorityTokenConstructedHereIsFalse =
        refl
    ; acceptedAuthorityExternalReceiptConstructedHere =
        false
    ; acceptedAuthorityExternalReceiptConstructedHereIsFalse =
        refl
    ; authorityTokenImpossibleHere =
        EXT.W3AcceptedAuthorityExternalReceiptCurrentStatus.acceptedAuthorityTokenUninhabited
          EXT.currentW3AcceptedAuthorityExternalReceiptStatus
    ; nonPromotionBoundary =
        "This is a token-only HEP-R55 intake request, not an accepted authority token"
        ∷ "The required evidence fields are public/source-bound and HEP-R53 runner-bound"
        ∷ "Repo governance does not permit self-issuance here because W3AcceptedEvidenceAuthorityToken is constructorless"
        ∷ "No W3AcceptedEvidenceAuthorityToken is constructed in this module"
        ∷ "No W3AcceptedAuthorityExternalReceipt is constructed in this module"
        ∷ []
    ; providerTraceabilityChecklist =
        "typedFirstMissing: Pack.missingAcceptedEvidenceAuthorityToken"
        ∷ "exactTokenType: DASHI.Physics.Closure.W3AcceptedEmpiricalAuthorityGate.W3AcceptedEvidenceAuthorityToken"
        ∷ "sourceTrace: HEPData dataset DOI 10.17182/hepdata.104472 and submission DOI 10.17182/hepdata.115656.v1"
        ∷ "tableTrace: ratio t43 and covariance t44"
        ∷ "runnerTrace: freeze commit 3205d746639568762c9e97adf4a3672c356bd491"
        ∷ "artifactTrace: per-bin artifact sha256 3987f82678943bab7679a9948e865f74f2263cdbe38a0e997734dad38939fda0"
        ∷ "projectionTrace: per-bin projection digest cc6ea1a8ea57ef376ae275c1b49e32b27d6d204d7b70cad5c6308b3f8a897a79"
        ∷ "witnessTrace: bin 12 pred 0.0486590199823977 data 0.049758 unc 0.00048197510309143566 pull -2.280159308132989"
        ∷ "boundaryTrace: token-only intake request; no accepted receipt, evidence-backed target, B4 promotion, origin promotion, W4/W5/W8 promotion, or broad unification claim"
        ∷ []
    ; providerInstruction =
        "External provider must supply DASHI.Physics.Closure.W3AcceptedEmpiricalAuthorityGate.W3AcceptedEvidenceAuthorityToken acknowledging the required evidence fields"
        ∷ "If the provider cannot supply the token, return a typed authority-unavailable or field-mismatch diagnostic"
        ∷ "The exact first missing provider field is Pack.missingAcceptedEvidenceAuthorityToken"
        ∷ "Do not treat public verifiability of the evidence fields as local construction of the accepted authority token"
        ∷ "Treat the handoff scope as limited SM+GR empirical coordination for the bounded t43 lane, not broad unification"
        ∷ []
    ; providerFacingHandoffPacket =
        "handoffStatus: finalProviderFacingHandoffPacketRequestOnly"
        ∷ "target: DASHI.Physics.Closure.W3AcceptedEmpiricalAuthorityGate.W3AcceptedEvidenceAuthorityToken"
        ∷ "firstMissingProviderField: Pack.missingAcceptedEvidenceAuthorityToken"
        ∷ "firstMissingType: DASHI.Physics.Closure.W3AcceptedEmpiricalAuthorityGate.W3AcceptedEvidenceAuthorityToken"
        ∷ "requestPack: DASHI.Physics.Closure.W3AcceptedAuthorityExternalReceiptRequestPack.canonicalW3AcceptedAuthorityExternalReceiptRequestPack"
        ∷ "currentExternalStatus: W3AcceptedAuthorityExternalReceipt obligation-only; no accepted external receipt constructed"
        ∷ "authorityEvidence: HEP-R53 runner per-bin non-collapse receipt plus public HEPData t43/t44 source fields"
        ∷ "traceabilityChecklist: providerTraceabilityChecklist"
        ∷ "claimScope: limited SM+GR empirical coordination for bounded below-Z t43, not broad unification"
        ∷ "providerResponse: supply the accepted authority token or return typed authority-unavailable/mismatch diagnostic"
        ∷ []
    ; providerFacingHandoffPacketIsFinal =
        true
    ; providerFacingHandoffPacketIsFinalIsTrue =
        refl
    ; exactFirstMissingBlocker =
        "W3AcceptedEvidenceAuthorityToken remains externally outstanding"
    ; exactFirstMissingStatus =
        "request-only final handoff; first missing = W3AcceptedEvidenceAuthorityToken; no W3AcceptedAuthorityExternalReceipt or W3AcceptedAuthorityPositiveRoute is constructed in repo"
    ; exactFirstMissingName =
        Pack.W3AcceptedAuthorityProviderPayloadRequest.exactAuthorityTokenName
          Pack.canonicalW3AcceptedAuthorityProviderPayloadRequest
    ; exactFirstMissingNameMatchesAuthorityTokenName =
        refl
    ; stillMissingPacketFields =
        []
    }

canonicalW3AcceptedEvidenceAuthorityTokenFirstMissing :
  W3AcceptedEvidenceAuthorityTokenFirstMissing
canonicalW3AcceptedEvidenceAuthorityTokenFirstMissing =
  W3AcceptedEvidenceAuthorityTokenIntakeRequest.firstMissing
    canonicalW3AcceptedEvidenceAuthorityTokenIntakeRequest

canonicalW3AcceptedEvidenceAuthorityTokenSelfIssuancePermitted :
  W3AcceptedEvidenceAuthorityTokenIntakeRequest.selfIssuancePermitted
    canonicalW3AcceptedEvidenceAuthorityTokenIntakeRequest
  ≡
  false
canonicalW3AcceptedEvidenceAuthorityTokenSelfIssuancePermitted = refl

canonicalW3AcceptedEvidenceAuthorityTokenConstructedHere :
  W3AcceptedEvidenceAuthorityTokenIntakeRequest.authorityTokenConstructedHere
    canonicalW3AcceptedEvidenceAuthorityTokenIntakeRequest
  ≡
  false
canonicalW3AcceptedEvidenceAuthorityTokenConstructedHere = refl

canonicalW3AcceptedEvidenceAuthorityTokenPacketReady :
  W3AcceptedEvidenceAuthorityTokenIntakeRequest.packetReadyForExternalAuthority
    canonicalW3AcceptedEvidenceAuthorityTokenIntakeRequest
  ≡
  true
canonicalW3AcceptedEvidenceAuthorityTokenPacketReady = refl

canonicalW3AcceptedEvidenceAuthorityTokenHandoffPacketFinal :
  W3AcceptedEvidenceAuthorityTokenIntakeRequest.providerFacingHandoffPacketIsFinal
    canonicalW3AcceptedEvidenceAuthorityTokenIntakeRequest
  ≡
  true
canonicalW3AcceptedEvidenceAuthorityTokenHandoffPacketFinal = refl

canonicalW3AcceptedEvidenceAuthorityTokenFirstMissingProviderField :
  W3AcceptedEvidenceAuthorityTokenIntakeRequest.exactFirstMissingProviderField
    canonicalW3AcceptedEvidenceAuthorityTokenIntakeRequest
  ≡
  Pack.missingAcceptedEvidenceAuthorityToken
canonicalW3AcceptedEvidenceAuthorityTokenFirstMissingProviderField = refl

canonicalW3AcceptedEvidenceAuthorityTokenStillMissingNoPacketFields :
  W3AcceptedEvidenceAuthorityTokenIntakeRequest.stillMissingPacketFields
    canonicalW3AcceptedEvidenceAuthorityTokenIntakeRequest
  ≡
  []
canonicalW3AcceptedEvidenceAuthorityTokenStillMissingNoPacketFields = refl
