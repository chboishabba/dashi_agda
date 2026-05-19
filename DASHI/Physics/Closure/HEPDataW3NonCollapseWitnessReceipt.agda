module DASHI.Physics.Closure.HEPDataW3NonCollapseWitnessReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.HEPDataExternalResidualWitnessPayload as Payload
import DASHI.Physics.Closure.HEPDataNonCollapseObservableObligation as NonCollapse
import DASHI.Physics.Closure.HEPDataObservableSchema as HEP
import DASHI.Physics.Closure.HEPDataResidualBridgeAuthorityGate as Gate
import DASHI.Physics.Closure.HEPDataResidualObservableClassReceiptProtoAlignment as Residual
import DASHI.Physics.Closure.HEPDataResidualProviderPayloadIntake as Intake
import DASHI.Physics.Closure.HEPDataResidualProviderReceiptRequestPack as Pack
import DASHI.Physics.Closure.HEPDataW3ComparisonLawReceipt as Comparison
import DASHI.Physics.Closure.W3AcceptedAuthorityExternalReceiptObligation as EXT
import DASHI.Physics.Closure.W3AcceptedAuthorityExternalReceiptRequestPack as Authority
import DASHI.Physics.Closure.W3T43AuthorityPacketCandidateDiagnostic as Candidate

------------------------------------------------------------------------
-- HEP-R53: W3 t43 non-collapse witness receipt route.
--
-- This module names the provider-grade t43 per-bin payload shape that can
-- close the nonCollapseWitnessReceipt slot after the runner emits per_bin and
-- numeric values.  It does not fabricate
-- HEPDataExternalNonCollapseWitnessReceipt, W3AcceptedEvidenceAuthorityToken,
-- or W3AcceptedAuthorityExternalReceipt.  The accepted target is reachable only
-- from a payload that already carries the constructorless external receipt and
-- an externally selected HEPData observable.

data HEPDataW3NonCollapseWitnessReceiptStatus : Set where
  blockedAwaitingProviderGradePerBinWitness :
    HEPDataW3NonCollapseWitnessReceiptStatus
  perBinRunnerWitnessExtracted :
    HEPDataW3NonCollapseWitnessReceiptStatus

data HEPDataW3T43PerBinWitnessField : Set where
  requiredPerBinArtifactPath :
    HEPDataW3T43PerBinWitnessField
  requiredPerBinArtifactSha256 :
    HEPDataW3T43PerBinWitnessField
  requiredProjectionDigest :
    HEPDataW3T43PerBinWitnessField
  requiredPerBinPayloadPresent :
    HEPDataW3T43PerBinWitnessField
  requiredT43DatasetAndTableBinding :
    HEPDataW3T43PerBinWitnessField
  requiredT44CovarianceTableBinding :
    HEPDataW3T43PerBinWitnessField
  requiredSelectedWitnessBin :
    HEPDataW3T43PerBinWitnessField
  requiredWitnessPhiStarLow :
    HEPDataW3T43PerBinWitnessField
  requiredWitnessPhiStarHigh :
    HEPDataW3T43PerBinWitnessField
  requiredWitnessPredictionValue :
    HEPDataW3T43PerBinWitnessField
  requiredWitnessDataValue :
    HEPDataW3T43PerBinWitnessField
  requiredWitnessResidualValue :
    HEPDataW3T43PerBinWitnessField
  requiredWitnessAbsResidualValue :
    HEPDataW3T43PerBinWitnessField
  requiredWitnessPullValue :
    HEPDataW3T43PerBinWitnessField
  requiredNonCollapseWitnessReceipt :
    HEPDataW3T43PerBinWitnessField
  requiredComparisonLawReceipt :
    HEPDataW3T43PerBinWitnessField
  requiredResidualProtoAlignmentDiagnostic :
    HEPDataW3T43PerBinWitnessField
  requiredAcceptedAuthorityRequestPack :
    HEPDataW3T43PerBinWitnessField

canonicalHEPDataW3T43PerBinWitnessFields :
  List HEPDataW3T43PerBinWitnessField
canonicalHEPDataW3T43PerBinWitnessFields =
  requiredPerBinArtifactPath
  ∷ requiredPerBinArtifactSha256
  ∷ requiredProjectionDigest
  ∷ requiredPerBinPayloadPresent
  ∷ requiredT43DatasetAndTableBinding
  ∷ requiredT44CovarianceTableBinding
  ∷ requiredSelectedWitnessBin
  ∷ requiredWitnessPhiStarLow
  ∷ requiredWitnessPhiStarHigh
  ∷ requiredWitnessPredictionValue
  ∷ requiredWitnessDataValue
  ∷ requiredWitnessResidualValue
  ∷ requiredWitnessAbsResidualValue
  ∷ requiredWitnessPullValue
  ∷ requiredNonCollapseWitnessReceipt
  ∷ requiredComparisonLawReceipt
  ∷ requiredResidualProtoAlignmentDiagnostic
  ∷ requiredAcceptedAuthorityRequestPack
  ∷ []

record HEPDataW3T43PerBinNonCollapseProviderPayload
  (observable : HEP.HEPDataObservable)
  : Setω where
  field
    externalNonCollapseWitnessReceipt :
      NonCollapse.HEPDataExternalNonCollapseWitnessReceipt

    nonCollapseWitness :
      NonCollapse.HEPDataNonCollapseWitness observable

    perBinArtifactPath :
      String

    perBinArtifactSha256 :
      String

    projectionDigest :
      String

    perBinPayloadPresent :
      Bool

    perBinPayloadPresentIsTrue :
      perBinPayloadPresent ≡ true

    datasetDOI :
      String

    ratioTableDOI :
      String

    covarianceTableDOI :
      String

    witnessBinIndex :
      String

    witnessPhiStarLow :
      Float

    witnessPhiStarHigh :
      Float

    witnessPrediction :
      Float

    witnessData :
      Float

    witnessResidual :
      Float

    witnessAbsResidual :
      Float

    witnessPull :
      Float

    numericNonCollapseClaim :
      String

    comparisonLawReceipt :
      Comparison.W3ComparisonLawReceipt

    residualProtoAlignment :
      Residual.HEPDataResidualObservableClassReceiptProtoAlignment

    acceptedAuthorityRequestPack :
      Authority.W3AcceptedAuthorityExternalReceiptRequestPack

    currentExternalReceiptStatus :
      EXT.W3AcceptedAuthorityExternalReceiptCurrentStatus

    candidateDiagnostic :
      Candidate.W3T43AuthorityPacketCandidateDiagnostic

payloadToExternalResidualWitnessPayload :
  {observable : HEP.HEPDataObservable} →
  HEPDataW3T43PerBinNonCollapseProviderPayload observable →
  Payload.HEPDataExternalResidualWitnessPayload observable
payloadToExternalResidualWitnessPayload payload =
  record
    { externalNonCollapseWitnessReceipt =
        HEPDataW3T43PerBinNonCollapseProviderPayload.externalNonCollapseWitnessReceipt
          payload
    ; nonCollapseWitness =
        HEPDataW3T43PerBinNonCollapseProviderPayload.nonCollapseWitness payload
    ; boundProviderReceipt =
        Pack.nonCollapseWitnessReceipt
    ; boundProviderReceiptIsNonCollapse =
        refl
    ; boundIntakePayloadField =
        Intake.payloadNonCollapseWitnessReceipt
    ; boundIntakePayloadFieldIsNonCollapse =
        refl
    ; boundGatePayloadField =
        Gate.gateRequiresNonCollapseWitness
    ; boundGatePayloadFieldIsNonCollapse =
        refl
    }

payloadToNonCollapseWitnessReceiptTarget :
  {observable : HEP.HEPDataObservable} →
  HEPDataW3T43PerBinNonCollapseProviderPayload observable →
  NonCollapse.HEPDataNonCollapseWitnessReceiptTarget observable
payloadToNonCollapseWitnessReceiptTarget payload =
  Payload.externalResidualWitnessPayloadToReceiptTarget
    (payloadToExternalResidualWitnessPayload payload)

w3T43PerBinProviderPayloadImpossibleHere :
  {observable : HEP.HEPDataObservable} →
  HEPDataW3T43PerBinNonCollapseProviderPayload observable →
  ⊥
w3T43PerBinProviderPayloadImpossibleHere payload =
  NonCollapse.externalNonCollapseWitnessReceiptImpossibleHere
    (HEPDataW3T43PerBinNonCollapseProviderPayload.externalNonCollapseWitnessReceipt
      payload)

record HEPDataW3NonCollapseWitnessReceiptRoute : Setω where
  field
    status :
      HEPDataW3NonCollapseWitnessReceiptStatus

    candidateDiagnostic :
      Candidate.W3T43AuthorityPacketCandidateDiagnostic

    residualProtoAlignment :
      Residual.HEPDataResidualObservableClassReceiptProtoAlignment

    comparisonLawReceipt :
      Comparison.W3ComparisonLawReceipt

    acceptedAuthorityRequestPack :
      Authority.W3AcceptedAuthorityExternalReceiptRequestPack

    currentExternalReceiptStatus :
      EXT.W3AcceptedAuthorityExternalReceiptCurrentStatus

    requiredProviderFields :
      List HEPDataW3T43PerBinWitnessField

    requiredProviderFieldsAreCanonical :
      requiredProviderFields
      ≡
      canonicalHEPDataW3T43PerBinWitnessFields

    currentRepoHasProviderGradePayload :
      Bool

    payloadToExternalPayload :
      {observable : HEP.HEPDataObservable} →
      HEPDataW3T43PerBinNonCollapseProviderPayload observable →
      Payload.HEPDataExternalResidualWitnessPayload observable

    payloadToReceiptTarget :
      {observable : HEP.HEPDataObservable} →
      HEPDataW3T43PerBinNonCollapseProviderPayload observable →
      NonCollapse.HEPDataNonCollapseWitnessReceiptTarget observable

    providerPayloadImpossibleHere :
      {observable : HEP.HEPDataObservable} →
      HEPDataW3T43PerBinNonCollapseProviderPayload observable →
      ⊥

    exactModuleShape :
      List String

    exactImports :
      List String

    remainingProviderRequirements :
      List String

    nonPromotionBoundary :
      List String

canonicalHEPDataW3NonCollapseWitnessReceiptRoute :
  HEPDataW3NonCollapseWitnessReceiptRoute
canonicalHEPDataW3NonCollapseWitnessReceiptRoute =
  record
    { status =
        blockedAwaitingProviderGradePerBinWitness
    ; candidateDiagnostic =
        Candidate.canonicalW3T43AuthorityPacketCandidateDiagnostic
    ; residualProtoAlignment =
        Residual.canonicalHEPDataResidualObservableClassReceiptProtoAlignment
    ; comparisonLawReceipt =
        Comparison.canonicalHEPDataW3ComparisonLawReceipt
    ; acceptedAuthorityRequestPack =
        Authority.canonicalW3AcceptedAuthorityExternalReceiptRequestPack
    ; currentExternalReceiptStatus =
        EXT.currentW3AcceptedAuthorityExternalReceiptStatus
    ; requiredProviderFields =
        canonicalHEPDataW3T43PerBinWitnessFields
    ; requiredProviderFieldsAreCanonical =
        refl
    ; currentRepoHasProviderGradePayload =
        false
    ; payloadToExternalPayload =
        payloadToExternalResidualWitnessPayload
    ; payloadToReceiptTarget =
        payloadToNonCollapseWitnessReceiptTarget
    ; providerPayloadImpossibleHere =
        w3T43PerBinProviderPayloadImpossibleHere
    ; exactModuleShape =
        "module DASHI.Physics.Closure.HEPDataW3NonCollapseWitnessReceipt where"
        ∷ "record HEPDataW3T43PerBinNonCollapseProviderPayload (observable : HEP.HEPDataObservable) : Setω"
        ∷ "payloadToExternalResidualWitnessPayload : provider payload -> HEPDataExternalResidualWitnessPayload observable"
        ∷ "payloadToNonCollapseWitnessReceiptTarget : provider payload -> HEPDataNonCollapseWitnessReceiptTarget observable"
        ∷ "record HEPDataW3NonCollapseWitnessReceiptRoute : Setω"
        ∷ "canonicalHEPDataW3NonCollapseWitnessReceiptRoute : non-promoting route diagnostic"
        ∷ []
    ; exactImports =
        "Agda.Builtin.Bool using (Bool; false; true)"
        ∷ "Agda.Builtin.Equality using (_≡_; refl)"
        ∷ "Agda.Builtin.Float using (Float)"
        ∷ "Agda.Builtin.String using (String)"
        ∷ "Agda.Primitive using (Setω)"
        ∷ "Data.Empty using (⊥)"
        ∷ "Data.List.Base using (List; _∷_; [])"
        ∷ "DASHI.Physics.Closure.HEPDataExternalResidualWitnessPayload as Payload"
        ∷ "DASHI.Physics.Closure.HEPDataNonCollapseObservableObligation as NonCollapse"
        ∷ "DASHI.Physics.Closure.HEPDataObservableSchema as HEP"
        ∷ "DASHI.Physics.Closure.HEPDataResidualBridgeAuthorityGate as Gate"
        ∷ "DASHI.Physics.Closure.HEPDataResidualObservableClassReceiptProtoAlignment as Residual"
        ∷ "DASHI.Physics.Closure.HEPDataResidualProviderPayloadIntake as Intake"
        ∷ "DASHI.Physics.Closure.HEPDataResidualProviderReceiptRequestPack as Pack"
        ∷ "DASHI.Physics.Closure.HEPDataW3ComparisonLawReceipt as Comparison"
        ∷ "DASHI.Physics.Closure.W3AcceptedAuthorityExternalReceiptObligation as EXT"
        ∷ "DASHI.Physics.Closure.W3AcceptedAuthorityExternalReceiptRequestPack as Authority"
        ∷ "DASHI.Physics.Closure.W3T43AuthorityPacketCandidateDiagnostic as Candidate"
        ∷ []
    ; remainingProviderRequirements =
        "W0 runner artifact must contain per_bin payload with extracted numeric values"
        ∷ "Provider payload must carry HEPDataExternalNonCollapseWitnessReceipt; this module does not construct it"
        ∷ "Provider payload must carry NonCollapse.HEPDataNonCollapseWitness for the externally selected HEPData observable"
        ∷ "Numeric witness fields must bind selected t43 bin, phi-star edges, prediction, data, residual, absolute residual, and pull"
        ∷ "W3AcceptedAuthorityExternalReceipt remains a later external authority receipt and is not constructed here"
        ∷ []
    ; nonPromotionBoundary =
        "This route is conditional on a provider payload; the canonical route has currentRepoHasProviderGradePayload = false"
        ∷ "The current repo still eliminates any attempted provider payload through the constructorless HEPDataExternalNonCollapseWitnessReceipt"
        ∷ "No W3AcceptedEvidenceAuthorityToken is fabricated here"
        ∷ "No W3AcceptedAuthorityExternalReceipt is fabricated here"
        ∷ "The existing bounded W3 comparison-law receipt is referenced, not widened beyond t43 below-Z"
        ∷ []
    }

canonicalHEPDataW3NonCollapseWitnessReceiptStatus :
  HEPDataW3NonCollapseWitnessReceiptStatus
canonicalHEPDataW3NonCollapseWitnessReceiptStatus =
  HEPDataW3NonCollapseWitnessReceiptRoute.status
    canonicalHEPDataW3NonCollapseWitnessReceiptRoute

record HEPDataW3T43RunnerPerBinNonCollapseReceipt : Setω where
  field
    status :
      HEPDataW3NonCollapseWitnessReceiptStatus

    lane :
      String

    candidate :
      Candidate.W3T43AuthorityPacketCandidateDiagnostic

    comparisonLawReceipt :
      Comparison.W3ComparisonLawReceipt

    perBinArtifactPath :
      String

    perBinArtifactSha256 :
      String

    perBinProjectionDigest :
      String

    priorArtifactSha256 :
      String

    predictionBinsStableAgainstPriorArtifact :
      Bool

    predictionBinsStableAgainstPriorArtifactIsTrue :
      predictionBinsStableAgainstPriorArtifact
      ≡
      true

    nBins :
      Float

    witnessBinIndex :
      Float

    witnessPhiStar :
      Float

    witnessPhiStarLow :
      Float

    witnessPhiStarHigh :
      Float

    witnessPrediction :
      Float

    witnessData :
      Float

    witnessUncertainty :
      Float

    witnessPull :
      Float

    witnessPullNonZero :
      Bool

    witnessPullNonZeroIsTrue :
      witnessPullNonZero
      ≡
      true

    witnessPredDataDistinct :
      Bool

    witnessPredDataDistinctIsTrue :
      witnessPredDataDistinct
      ≡
      true

    comparisonChi2PerDof :
      Float

    authorityTokenConstructedHere :
      Bool

    acceptedAuthorityExternalReceiptConstructedHere :
      Bool

    nextReceipt :
      String

    nonPromotionBoundary :
      List String

canonicalHEPDataW3T43RunnerPerBinNonCollapseReceipt :
  HEPDataW3T43RunnerPerBinNonCollapseReceipt
canonicalHEPDataW3T43RunnerPerBinNonCollapseReceipt =
  record
    { status =
        perBinRunnerWitnessExtracted
    ; lane =
        "T43BelowZMassWindowRatio"
    ; candidate =
        Candidate.canonicalW3T43AuthorityPacketCandidateDiagnostic
    ; comparisonLawReceipt =
        Comparison.canonicalHEPDataW3ComparisonLawReceipt
    ; perBinArtifactPath =
        "/tmp/t43_clean_freeze_v2.json"
    ; perBinArtifactSha256 =
        "3987f82678943bab7679a9948e865f74f2263cdbe38a0e997734dad38939fda0"
    ; perBinProjectionDigest =
        "cc6ea1a8ea57ef376ae275c1b49e32b27d6d204d7b70cad5c6308b3f8a897a79"
    ; priorArtifactSha256 =
        "ffd659e6e2f271d75ec6bf90c5be34cbb9959a8f9d32762c1a2231835fb61eac"
    ; predictionBinsStableAgainstPriorArtifact =
        true
    ; predictionBinsStableAgainstPriorArtifactIsTrue =
        refl
    ; nBins =
        18.0
    ; witnessBinIndex =
        12.0
    ; witnessPhiStar =
        0.10250000000000001
    ; witnessPhiStarLow =
        0.091
    ; witnessPhiStarHigh =
        0.114
    ; witnessPrediction =
        0.0486590199823977
    ; witnessData =
        0.049758
    ; witnessUncertainty =
        0.00048197510309143566
    ; witnessPull =
        -2.280159308132989
    ; witnessPullNonZero =
        true
    ; witnessPullNonZeroIsTrue =
        refl
    ; witnessPredDataDistinct =
        true
    ; witnessPredDataDistinctIsTrue =
        refl
    ; comparisonChi2PerDof =
        2.1565191176
    ; authorityTokenConstructedHere =
        false
    ; acceptedAuthorityExternalReceiptConstructedHere =
        false
    ; nextReceipt =
        "HEP-R54: assemble W3AcceptedAuthorityExternalReceipt from the comparison law, residual proto alignment, per-bin non-collapse witness, and external accepted authority token"
    ; nonPromotionBoundary =
        "HEP-R53 supplies runner per-bin non-collapse evidence"
        ∷ "It does not construct W3AcceptedEvidenceAuthorityToken"
        ∷ "It does not construct W3AcceptedAuthorityExternalReceipt"
        ∷ "It does not widen the bounded t43 comparison-law receipt"
        ∷ []
    }

canonicalHEPDataW3T43RunnerPerBinWitnessPullNonZero :
  HEPDataW3T43RunnerPerBinNonCollapseReceipt.witnessPullNonZero
    canonicalHEPDataW3T43RunnerPerBinNonCollapseReceipt
    ≡
    true
canonicalHEPDataW3T43RunnerPerBinWitnessPullNonZero = refl

canonicalHEPDataW3T43RunnerPerBinWitnessPredDataDistinct :
  HEPDataW3T43RunnerPerBinNonCollapseReceipt.witnessPredDataDistinct
    canonicalHEPDataW3T43RunnerPerBinNonCollapseReceipt
    ≡
    true
canonicalHEPDataW3T43RunnerPerBinWitnessPredDataDistinct = refl
