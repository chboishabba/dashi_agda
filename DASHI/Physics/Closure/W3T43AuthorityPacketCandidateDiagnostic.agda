module DASHI.Physics.Closure.W3T43AuthorityPacketCandidateDiagnostic where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.HEPDataResidualObservableClassReceiptProtoAlignment as Residual
import DASHI.Physics.Closure.W3AcceptedAuthorityExternalReceiptObligation as EXT
import DASHI.Physics.Closure.W3AcceptedAuthorityExternalReceiptRequestPack as Request

------------------------------------------------------------------------
-- W3 t43 authority-packet candidate diagnostic.
--
-- This is the Curie-W3 authority-packet round output.  It records the strongest
-- checksum-bound local non-collapse candidate available in
-- /tmp/t43_clean_freeze.json, but does not construct the provider-grade
-- residualObservableClassReceipt, nonCollapseWitnessReceipt,
-- W3AcceptedEvidenceAuthorityToken, or W3AcceptedAuthorityExternalReceipt.

data W3T43AuthorityPacketCandidateStatus : Set where
  localT43WitnessCandidateFoundButPerBinProviderPayloadMissing :
    W3T43AuthorityPacketCandidateStatus

data W3T43AuthorityPacketComponent : Set where
  componentResidualObservableClassReceipt :
    W3T43AuthorityPacketComponent
  componentNonCollapseWitnessReceipt :
    W3T43AuthorityPacketComponent
  componentAcceptedEvidenceAuthorityToken :
    W3T43AuthorityPacketComponent
  componentAcceptedAuthorityExternalReceipt :
    W3T43AuthorityPacketComponent

canonicalW3T43AuthorityPacketComponents :
  List W3T43AuthorityPacketComponent
canonicalW3T43AuthorityPacketComponents =
  componentResidualObservableClassReceipt
  ∷ componentNonCollapseWitnessReceipt
  ∷ componentAcceptedEvidenceAuthorityToken
  ∷ componentAcceptedAuthorityExternalReceipt
  ∷ []

record W3T43LocalNonCollapseWitnessCandidate : Set where
  field
    artifactPath :
      String

    artifactSha256 :
      String

    projectionDigest :
      String

    artifactHasPerBinPayload :
      Bool

    fallbackPayloadSource :
      String

    binCount :
      String

    witnessBinIndex :
      String

    witnessPhiStarLow :
      String

    witnessPhiStarHigh :
      String

    witnessPhiStar :
      String

    witnessPrediction :
      String

    witnessData :
      String

    witnessResidual :
      String

    witnessAbsResidual :
      String

    witnessInequality :
      String

    providerGradePayloadStillNeeded :
      String

canonicalW3T43LocalNonCollapseWitnessCandidate :
  W3T43LocalNonCollapseWitnessCandidate
canonicalW3T43LocalNonCollapseWitnessCandidate =
  record
    { artifactPath =
        "/tmp/t43_clean_freeze.json"
    ; artifactSha256 =
        "ffd659e6e2f271d75ec6bf90c5be34cbb9959a8f9d32762c1a2231835fb61eac"
    ; projectionDigest =
        "00f6c23f97f9c0275d90e6ffbf6151b07defcc163708e2d93982d9b7d6866035"
    ; artifactHasPerBinPayload =
        false
    ; fallbackPayloadSource =
        "artifact.bins entries with R_dashi, R_data, and residual; per_bin/pull payload absent"
    ; binCount =
        "18"
    ; witnessBinIndex =
        "17"
    ; witnessPhiStarLow =
        "1.153"
    ; witnessPhiStarHigh =
        "3.277"
    ; witnessPhiStar =
        "2.215"
    ; witnessPrediction =
        "0.07610793309784744"
    ; witnessData =
        "0.078012"
    ; witnessResidual =
        "-0.001904066902152557"
    ; witnessAbsResidual =
        "0.001904066902152557"
    ; witnessInequality =
        "0.07610793309784744 != 0.078012"
    ; providerGradePayloadStillNeeded =
        "per_bin/pull-bearing verbose artifact or external provider payload must bind this triple before nonCollapseWitnessReceipt can be accepted"
    }

record W3T43AuthorityPacketCandidateDiagnostic : Setω where
  field
    status :
      W3T43AuthorityPacketCandidateStatus

    residualProtoAlignment :
      Residual.HEPDataResidualObservableClassReceiptProtoAlignment

    acceptedAuthorityRequestPack :
      Request.W3AcceptedAuthorityExternalReceiptRequestPack

    currentExternalReceiptStatus :
      EXT.W3AcceptedAuthorityExternalReceiptCurrentStatus

    packetComponents :
      List W3T43AuthorityPacketComponent

    packetComponentsAreCanonical :
      packetComponents
      ≡
      canonicalW3T43AuthorityPacketComponents

    localWitnessCandidate :
      W3T43LocalNonCollapseWitnessCandidate

    datasetDOI :
      String

    paperDOI :
      String

    ratioTableDOI :
      String

    covarianceTableDOI :
      String

    observableConvention :
      String

    freezeCommit :
      String

    exactRerunNeededForProviderPayload :
      String

    authorityReceiptConstructibleHere :
      Bool

    w3PromotionConstructedHere :
      Bool

    remainingMissingReceipts :
      List String

    nonPromotionBoundary :
      List String

canonicalW3T43AuthorityPacketCandidateDiagnostic :
  W3T43AuthorityPacketCandidateDiagnostic
canonicalW3T43AuthorityPacketCandidateDiagnostic =
  record
    { status =
        localT43WitnessCandidateFoundButPerBinProviderPayloadMissing
    ; residualProtoAlignment =
        Residual.canonicalHEPDataResidualObservableClassReceiptProtoAlignment
    ; acceptedAuthorityRequestPack =
        Request.canonicalW3AcceptedAuthorityExternalReceiptRequestPack
    ; currentExternalReceiptStatus =
        EXT.currentW3AcceptedAuthorityExternalReceiptStatus
    ; packetComponents =
        canonicalW3T43AuthorityPacketComponents
    ; packetComponentsAreCanonical =
        refl
    ; localWitnessCandidate =
        canonicalW3T43LocalNonCollapseWitnessCandidate
    ; datasetDOI =
        "10.17182/hepdata.104472"
    ; paperDOI =
        "10.1140/epjc/s10052-023-11631-7"
    ; ratioTableDOI =
        "10.17182/hepdata.115656.v1/t43"
    ; covarianceTableDOI =
        "10.17182/hepdata.115656.v1/t44"
    ; observableConvention =
        "UnnormalizedDifferentialCrossSectionRatio"
    ; freezeCommit =
        "3205d746639568762c9e97adf4a3672c356bd491"
    ; exactRerunNeededForProviderPayload =
        "python3 scripts/run_t43_projection.py --freeze-hash 3205d746639568762c9e97adf4a3672c356bd491 --prediction-api DASHI.Physics.Prediction.sigma_dashi:predict_ratio --output /tmp/t43_clean_freeze_v2.json"
    ; authorityReceiptConstructibleHere =
        false
    ; w3PromotionConstructedHere =
        false
    ; remainingMissingReceipts =
        "HEPDataResidualObservableClassReceipt accepted by provider"
        ∷ "nonCollapseWitnessReceipt bound to per_bin or provider payload"
        ∷ "W3AcceptedEvidenceAuthorityToken"
        ∷ "W3AcceptedAuthorityExternalReceipt"
        ∷ []
    ; nonPromotionBoundary =
        "The checksum-bound local artifact gives a concrete non-zero residual candidate, not an accepted provider receipt"
        ∷ "The artifact lacks per_bin/pull payload, so the provider-grade nonCollapseWitnessReceipt remains missing"
        ∷ "The accepted authority token is constructorless in the current repo"
        ∷ "This diagnostic does not promote W3 beyond the already bounded t43 state"
        ∷ []
    }
