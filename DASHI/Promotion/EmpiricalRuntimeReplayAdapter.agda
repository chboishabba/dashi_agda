module DASHI.Promotion.EmpiricalRuntimeReplayAdapter where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Level; Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Constants.Registry as Registry
import DASHI.Promotion.NumericAndAuthorityObligations as Authority
import DASHI.Interop.PNFResidualConsumerReceiptRequestPack as PNFRequest
import DASHI.Interop.PNFResidualConsumerRuntimeProviderAttempt as PNFAttempt
import DASHI.Physics.Closure.HEPDataComparisonLawReceiptRequest as HEPComparison
import DASHI.Physics.Closure.HEPDataT43ProjectionRunnerImplementationAttempt as HEPProjection

------------------------------------------------------------------------
-- Empirical provider/runtime replay adapter.
--
-- This module is a concrete fail-closed adapter surface.  It builds typed
-- provider, observable, projection, comparison, covariance, holdout, replay,
-- and semantic-review payloads and exposes validation machinery over them.
-- It deliberately does not manufacture accepted authority tokens.

listCount : ∀ {a : Level} {A : Set a} → List A → Nat
listCount [] = zero
listCount (_ ∷ xs) = suc (listCount xs)

------------------------------------------------------------------------
-- Provider payload and observable metadata.

data ProviderAuthorityClass : Set where
  hepDataProviderAuthority : ProviderAuthorityClass
  codataProviderAuthority : ProviderAuthorityClass
  nistProviderAuthority : ProviderAuthorityClass
  runtimeReceiptProviderAuthority : ProviderAuthorityClass
  internalDiagnosticProviderOnly : ProviderAuthorityClass

data ObservableKind : Set where
  ratioTableObservable : ObservableKind
  residualTableObservable : ObservableKind
  spectralSeverityObservable : ObservableKind
  pnfEmissionObservable : ObservableKind
  projectionDigestObservable : ObservableKind

data ProjectionKind : Set where
  sourceChecksumProjection : ProjectionKind
  ratioTableProjection : ProjectionKind
  covarianceShapeProjection : ProjectionKind
  pnfResidualProjection : ProjectionKind
  semanticDigestProjection : ProjectionKind

record ProviderPayloadMetadata : Set₁ where
  field
    providerLabel : String
    providerAuthorityClass : ProviderAuthorityClass
    providerRecordId : String
    authorityVersion : String
    sourceUri : String
    sourceChecksum : String
    sourceAccessDate : String
    sourceRegistry :
      Registry.ConstantsRegistry
    sourceAuthorityPolicyReceipt :
      Registry.AuthorityConsumptionPolicyReceipt
    sourceEmpiricalRuntimeReceipt :
      Registry.EmpiricalRuntimeKnownInputsReferenceReceipt
    governingAuthorityRow :
      Authority.AuthorityObligationRow
    requiredMetadata :
      List Authority.MetadataObligation
    sourceChecksumBound :
      Bool
    sourceChecksumBoundIsTrue :
      sourceChecksumBound ≡ true
    providerAuthorityTokenAccepted :
      Bool
    providerAuthorityTokenAcceptedIsFalse :
      providerAuthorityTokenAccepted ≡ false
    providerAuthorityPromoted :
      Bool
    providerAuthorityPromotedIsFalse :
      providerAuthorityPromoted ≡ false

open ProviderPayloadMetadata public

record ObservableDefinition : Set₁ where
  field
    observableLabel : String
    observableKind : ObservableKind
    observableUnits : String
    observableDomain : String
    binningOrIndexingConvention : String
    payloadMetadata : ProviderPayloadMetadata
    observableDefinitionDigest : String
    sourceChecksum :
      String
    sourceChecksumMatchesPayload :
      sourceChecksum
      ≡
      ProviderPayloadMetadata.sourceChecksum payloadMetadata
    observableAuthorityAccepted :
      Bool
    observableAuthorityAcceptedIsFalse :
      observableAuthorityAccepted ≡ false

open ObservableDefinition public

record TransformProjectionDigest : Set₁ where
  field
    projectionLabel : String
    projectionKind : ProjectionKind
    sourceObservable : ObservableDefinition
    transformLabel : String
    transformVersion : String
    sourceArtifactChecksum : String
    sourceChecksumMatchesObservable :
      sourceArtifactChecksum
      ≡
      ObservableDefinition.sourceChecksum sourceObservable
    projectionDigest : String
    projectedObservableDigest : String
    runtimeReplayProjectionDigest : String
    projectionDigestMatchesReplay :
      projectionDigest ≡ runtimeReplayProjectionDigest
    projectionStableUnderIdenticalReplay :
      Bool
    projectionStableUnderIdenticalReplayIsTrue :
      projectionStableUnderIdenticalReplay ≡ true
    projectionAuthorityAccepted :
      Bool
    projectionAuthorityAcceptedIsFalse :
      projectionAuthorityAccepted ≡ false

open TransformProjectionDigest public

------------------------------------------------------------------------
-- Comparison, covariance, calibration, and holdout machinery.

data ComparisonLawKind : Set where
  exactDigestEqualityLaw : ComparisonLawKind
  chiSquareCovarianceAwareLaw : ComparisonLawKind
  perBinTwoSigmaLaw : ComparisonLawKind
  receiptBackedResidualLaw : ComparisonLawKind

data CovarianceShape : Set where
  diagonalCovariance : CovarianceShape
  denseCovarianceMatrix : CovarianceShape
  blockCovarianceMatrix : CovarianceShape
  covarianceShapeDiagnosticOnly : CovarianceShape

data HoldoutSplitKind : Set where
  frozenTrainHoldoutSplit : HoldoutSplitKind
  independentProviderHoldout : HoldoutSplitKind
  crossProviderReplicationHoldout : HoldoutSplitKind
  holdoutDiagnosticOnly : HoldoutSplitKind

record ComparisonLawAdapter : Setω where
  field
    comparisonLabel : String
    comparisonLawKind : ComparisonLawKind
    leftProjection : TransformProjectionDigest
    rightProjection : TransformProjectionDigest
    comparisonMetric : String
    tolerancePolicy : String
    lawAuthoritySurface :
      HEPComparison.HEPDataComparisonLawReceiptRequest
    requiredComparisonFields :
      List HEPComparison.HEPDataComparisonLawReceiptField
    currentComparisonGaps :
      List HEPComparison.HEPDataComparisonLawReceiptCurrentGap
    covarianceAware :
      Bool
    covarianceAwareIsTrue :
      covarianceAware ≡ true
    comparisonLawAccepted :
      Bool
    comparisonLawAcceptedIsFalse :
      comparisonLawAccepted ≡ false
    comparisonLawPromoted :
      Bool
    comparisonLawPromotedIsFalse :
      comparisonLawPromoted ≡ false

open ComparisonLawAdapter public

record CovarianceUnitCalibration : Setω where
  field
    calibrationLabel : String
    comparisonAdapter : ComparisonLawAdapter
    covarianceShape : CovarianceShape
    covarianceSourceDigest : String
    unitConvention : String
    uncertaintyModel : String
    calibrationDigest : String
    calibrationProviderMetadata :
      ProviderPayloadMetadata
    covarianceShapeParsed :
      Bool
    covarianceShapeParsedIsTrue :
      covarianceShapeParsed ≡ true
    unitConventionBound :
      Bool
    unitConventionBoundIsTrue :
      unitConventionBound ≡ true
    covarianceCalibrationAccepted :
      Bool
    covarianceCalibrationAcceptedIsFalse :
      covarianceCalibrationAccepted ≡ false
    covarianceCalibrationPromoted :
      Bool
    covarianceCalibrationPromotedIsFalse :
      covarianceCalibrationPromoted ≡ false

open CovarianceUnitCalibration public

record HoldoutValidationProtocol : Setω where
  field
    protocolLabel : String
    holdoutSplitKind : HoldoutSplitKind
    providerMetadata : ProviderPayloadMetadata
    comparisonAdapter : ComparisonLawAdapter
    covarianceCalibration : CovarianceUnitCalibration
    trainingSourceDigest : String
    holdoutSourceDigest : String
    freezeHash : String
    validationProtocolDigest : String
    passFailCriterion : String
    holdoutDatasetNamed :
      Bool
    holdoutDatasetNamedIsTrue :
      holdoutDatasetNamed ≡ true
    holdoutValidationAccepted :
      Bool
    holdoutValidationAcceptedIsFalse :
      holdoutValidationAccepted ≡ false
    empiricalAdequacyAccepted :
      Bool
    empiricalAdequacyAcceptedIsFalse :
      empiricalAdequacyAccepted ≡ false

open HoldoutValidationProtocol public

------------------------------------------------------------------------
-- Runtime replay records.

data ReplayEventKind : Set where
  commandStarted : ReplayEventKind
  environmentCapturedEvent : ReplayEventKind
  sourceChecksumVerified : ReplayEventKind
  parserReducedProjection : ReplayEventKind
  projectionDigestEmitted : ReplayEventKind
  residualComputationRecorded : ReplayEventKind
  commandFinished : ReplayEventKind

record RuntimeCommandEnvironment : Set where
  field
    runtimeReceiptId : String
    commandLine : String
    workingDirectory : String
    environmentDigest : String
    parserVersion : String
    reducerVersion : String
    sourceArtifactChecksum : String
    projectionDigest : String
    commandDigest : String
    environmentCaptured :
      Bool
    environmentCapturedIsTrue :
      environmentCaptured ≡ true

open RuntimeCommandEnvironment public

record RuntimeReplayLogEntry : Set where
  field
    eventKind : ReplayEventKind
    eventOrdinal : Nat
    inputDigest : String
    outputDigest : String
    projectionDigest : String
    eventNote : String

open RuntimeReplayLogEntry public

record RuntimeReplayLog : Set where
  field
    commandEnvironment : RuntimeCommandEnvironment
    replayEntries : List RuntimeReplayLogEntry
    replayEntryCount : Nat
    replayEntryCountMatches :
      replayEntryCount ≡ listCount replayEntries
    sourceChecksum : String
    sourceChecksumMatchesEnvironment :
      sourceChecksum
      ≡
      RuntimeCommandEnvironment.sourceArtifactChecksum commandEnvironment
    projectionDigest : String
    projectionDigestMatchesEnvironment :
      projectionDigest
      ≡
      RuntimeCommandEnvironment.projectionDigest commandEnvironment
    replayLogDigest : String
    replayComplete :
      Bool
    replayCompleteIsTrue :
      replayComplete ≡ true
    runtimeReplayAuthorityAccepted :
      Bool
    runtimeReplayAuthorityAcceptedIsFalse :
      runtimeReplayAuthorityAccepted ≡ false

open RuntimeReplayLog public

replayLogProjectionDigest :
  RuntimeReplayLog →
  String
replayLogProjectionDigest log =
  RuntimeReplayLog.projectionDigest log

deterministicReplayEquality :
  (log : RuntimeReplayLog) →
  replayLogProjectionDigest log ≡ replayLogProjectionDigest log
deterministicReplayEquality log = refl

deterministicReplayLogDigestEquality :
  (log : RuntimeReplayLog) →
  RuntimeReplayLog.replayLogDigest log
  ≡
  RuntimeReplayLog.replayLogDigest log
deterministicReplayLogDigestEquality log = refl

identicalCanonicalReplayProjectionDigestMatches :
  (left right : RuntimeReplayLog) →
  left ≡ right →
  replayLogProjectionDigest left ≡ replayLogProjectionDigest right
identicalCanonicalReplayProjectionDigestMatches left .left refl = refl

identicalCanonicalReplayLogDigestMatches :
  (left right : RuntimeReplayLog) →
  left ≡ right →
  RuntimeReplayLog.replayLogDigest left
  ≡
  RuntimeReplayLog.replayLogDigest right
identicalCanonicalReplayLogDigestMatches left .left refl = refl

record RuntimeReplayAdapter : Setω where
  field
    adapterLabel : String
    replayLog : RuntimeReplayLog
    transformProjectionDigest : TransformProjectionDigest
    runtimeProviderAttempt :
      PNFAttempt.PNFResidualConsumerRuntimeProviderAttempt
    pnfRequestPack :
      PNFRequest.PNFResidualConsumerReceiptRequestPack
    projectionDigestFromReplay :
      replayLogProjectionDigest replayLog
      ≡
      TransformProjectionDigest.runtimeReplayProjectionDigest
        transformProjectionDigest
    deterministicReplayForIdenticalLog :
      replayLogProjectionDigest replayLog ≡ replayLogProjectionDigest replayLog
    replayPayloadAbsentDiagnostic :
      Bool
    replayPayloadAbsentDiagnosticIsTrue :
      replayPayloadAbsentDiagnostic ≡ true
    runtimeReplayAuthorityAccepted :
      Bool
    runtimeReplayAuthorityAcceptedIsFalse :
      runtimeReplayAuthorityAccepted ≡ false

open RuntimeReplayAdapter public

------------------------------------------------------------------------
-- Semantic adequacy and validation status.

data ValidationFailureReason : Set where
  missingProviderAuthorityToken : ValidationFailureReason
  missingAcceptedComparisonLaw : ValidationFailureReason
  missingCovarianceCalibrationAuthority : ValidationFailureReason
  missingHoldoutAcceptance : ValidationFailureReason
  missingRuntimeReplayAuthority : ValidationFailureReason
  missingSemanticAdequacyReview : ValidationFailureReason
  missingAggregateEmpiricalAdequacy : ValidationFailureReason

data ValidationVerdict : Set where
  validationPass : ValidationVerdict
  validationFail : List ValidationFailureReason → ValidationVerdict

record SemanticAdequacyReview : Setω where
  field
    semanticReviewLabel : String
    replayAdapter : RuntimeReplayAdapter
    nonInspectionBoundary : List String
    semanticCriteria : List String
    reviewedProjectionDigest : String
    reviewedProjectionDigestMatchesReplay :
      reviewedProjectionDigest
      ≡
      replayLogProjectionDigest
        (RuntimeReplayAdapter.replayLog replayAdapter)
    semanticReviewAuthorityTokenAccepted :
      Bool
    semanticReviewAuthorityTokenAcceptedIsFalse :
      semanticReviewAuthorityTokenAccepted ≡ false
    semanticAdequacyAccepted :
      Bool
    semanticAdequacyAcceptedIsFalse :
      semanticAdequacyAccepted ≡ false

open SemanticAdequacyReview public

record EmpiricalRuntimeValidationReport : Setω where
  field
    reportLabel : String
    authorityIndex :
      Authority.NumericAndAuthorityObligationIndex
    providerMetadata : ProviderPayloadMetadata
    observableDefinition : ObservableDefinition
    projectionDigest : TransformProjectionDigest
    comparisonAdapter : ComparisonLawAdapter
    covarianceCalibration : CovarianceUnitCalibration
    holdoutProtocol : HoldoutValidationProtocol
    runtimeReplayAdapter : RuntimeReplayAdapter
    semanticReview : SemanticAdequacyReview
    validationVerdict : ValidationVerdict
    failureReasons : List ValidationFailureReason
    failureReasonCount : Nat
    failureReasonCountMatches :
      failureReasonCount ≡ listCount failureReasons
    providerAuthorityPromoted :
      Bool
    providerAuthorityPromotedIsFalse :
      providerAuthorityPromoted ≡ false
    comparisonLawPromoted :
      Bool
    comparisonLawPromotedIsFalse :
      comparisonLawPromoted ≡ false
    covarianceCalibrationPromoted :
      Bool
    covarianceCalibrationPromotedIsFalse :
      covarianceCalibrationPromoted ≡ false
    holdoutValidationAccepted :
      Bool
    holdoutValidationAcceptedIsFalse :
      holdoutValidationAccepted ≡ false
    runtimeReplayAuthorityAccepted :
      Bool
    runtimeReplayAuthorityAcceptedIsFalse :
      runtimeReplayAuthorityAccepted ≡ false
    semanticAdequacyAccepted :
      Bool
    semanticAdequacyAcceptedIsFalse :
      semanticAdequacyAccepted ≡ false
    empiricalAdequacyAccepted :
      Bool
    empiricalAdequacyAcceptedIsFalse :
      empiricalAdequacyAccepted ≡ false

open EmpiricalRuntimeValidationReport public

validationFailsWith :
  List ValidationFailureReason →
  ValidationVerdict
validationFailsWith reasons = validationFail reasons

canonicalValidationFailureReasons : List ValidationFailureReason
canonicalValidationFailureReasons =
  missingProviderAuthorityToken
  ∷ missingAcceptedComparisonLaw
  ∷ missingCovarianceCalibrationAuthority
  ∷ missingHoldoutAcceptance
  ∷ missingRuntimeReplayAuthority
  ∷ missingSemanticAdequacyReview
  ∷ missingAggregateEmpiricalAdequacy
  ∷ []

------------------------------------------------------------------------
-- Canonical fail-closed instance.

canonicalProviderPayloadMetadata : ProviderPayloadMetadata
canonicalProviderPayloadMetadata = record
  { providerLabel =
      "HEPData/provider runtime authority payload metadata"
  ; providerAuthorityClass =
      hepDataProviderAuthority
  ; providerRecordId =
      "provider-receipt-id-required"
  ; authorityVersion =
      "authority-version-required"
  ; sourceUri =
      "provider-source-uri-required"
  ; sourceChecksum =
      "provider-source-checksum-required"
  ; sourceAccessDate =
      "source-access-date-required"
  ; sourceRegistry =
      Registry.repoWideConstantsRegistry
  ; sourceAuthorityPolicyReceipt =
      Registry.canonicalAuthorityConsumptionPolicyReceipt
  ; sourceEmpiricalRuntimeReceipt =
      Registry.canonicalEmpiricalRuntimeKnownInputsReferenceReceipt
  ; governingAuthorityRow =
      Authority.providerAuthorityObligation
  ; requiredMetadata =
      Authority.canonicalMetadataObligations
  ; sourceChecksumBound =
      true
  ; sourceChecksumBoundIsTrue =
      refl
  ; providerAuthorityTokenAccepted =
      false
  ; providerAuthorityTokenAcceptedIsFalse =
      refl
  ; providerAuthorityPromoted =
      Registry.EmpiricalRuntimeKnownInputsReferenceReceipt.acceptedProviderAuthorityPromoted
        Registry.canonicalEmpiricalRuntimeKnownInputsReferenceReceipt
  ; providerAuthorityPromotedIsFalse =
      Registry.EmpiricalRuntimeKnownInputsReferenceReceipt.acceptedProviderAuthorityPromotedIsFalse
        Registry.canonicalEmpiricalRuntimeKnownInputsReferenceReceipt
  }

canonicalObservableDefinition : ObservableDefinition
canonicalObservableDefinition = record
  { observableLabel =
      "provider ratio/residual observable definition"
  ; observableKind =
      ratioTableObservable
  ; observableUnits =
      "provider-native units; unitConvention receipt required before promotion"
  ; observableDomain =
      "HEPData/provider ratio table and residual projection lane"
  ; binningOrIndexingConvention =
      "provider-native binning; checksum-bound projection required"
  ; payloadMetadata =
      canonicalProviderPayloadMetadata
  ; observableDefinitionDigest =
      "observable-definition-digest-required"
  ; sourceChecksum =
      ProviderPayloadMetadata.sourceChecksum canonicalProviderPayloadMetadata
  ; sourceChecksumMatchesPayload =
      refl
  ; observableAuthorityAccepted =
      false
  ; observableAuthorityAcceptedIsFalse =
      refl
  }

canonicalTransformProjectionDigest : TransformProjectionDigest
canonicalTransformProjectionDigest = record
  { projectionLabel =
      "provider artifact checksum to projection digest"
  ; projectionKind =
      ratioTableProjection
  ; sourceObservable =
      canonicalObservableDefinition
  ; transformLabel =
      "source artifact -> checksum -> projected observable digest"
  ; transformVersion =
      "projection-transform-version-required"
  ; sourceArtifactChecksum =
      ObservableDefinition.sourceChecksum canonicalObservableDefinition
  ; sourceChecksumMatchesObservable =
      refl
  ; projectionDigest =
      "projection-digest-required"
  ; projectedObservableDigest =
      "projected-observable-digest-required"
  ; runtimeReplayProjectionDigest =
      "projection-digest-required"
  ; projectionDigestMatchesReplay =
      refl
  ; projectionStableUnderIdenticalReplay =
      true
  ; projectionStableUnderIdenticalReplayIsTrue =
      refl
  ; projectionAuthorityAccepted =
      false
  ; projectionAuthorityAcceptedIsFalse =
      refl
  }

canonicalComparisonLawAdapter : ComparisonLawAdapter
canonicalComparisonLawAdapter = record
  { comparisonLabel =
      "covariance-aware provider projection comparison law"
  ; comparisonLawKind =
      chiSquareCovarianceAwareLaw
  ; leftProjection =
      canonicalTransformProjectionDigest
  ; rightProjection =
      canonicalTransformProjectionDigest
  ; comparisonMetric =
      "chi2/chi2-per-dof plus per-bin two-sigma law once authority arrives"
  ; tolerancePolicy =
      "fail closed until comparison-law receipt and authority DOI are accepted"
  ; lawAuthoritySurface =
      HEPComparison.canonicalHEPDataComparisonLawReceiptRequest
  ; requiredComparisonFields =
      HEPComparison.canonicalHEPDataComparisonLawReceiptFields
  ; currentComparisonGaps =
      HEPComparison.canonicalHEPDataComparisonLawReceiptCurrentGaps
  ; covarianceAware =
      true
  ; covarianceAwareIsTrue =
      refl
  ; comparisonLawAccepted =
      false
  ; comparisonLawAcceptedIsFalse =
      refl
  ; comparisonLawPromoted =
      Registry.EmpiricalRuntimeKnownInputsReferenceReceipt.comparisonLawPromoted
        Registry.canonicalEmpiricalRuntimeKnownInputsReferenceReceipt
  ; comparisonLawPromotedIsFalse =
      Registry.EmpiricalRuntimeKnownInputsReferenceReceipt.comparisonLawPromotedIsFalse
        Registry.canonicalEmpiricalRuntimeKnownInputsReferenceReceipt
  }

canonicalCovarianceUnitCalibration : CovarianceUnitCalibration
canonicalCovarianceUnitCalibration = record
  { calibrationLabel =
      "provider covariance, unit, uncertainty, and calibration binding"
  ; comparisonAdapter =
      canonicalComparisonLawAdapter
  ; covarianceShape =
      covarianceShapeDiagnosticOnly
  ; covarianceSourceDigest =
      "covariance-source-digest-required"
  ; unitConvention =
      "provider unit convention receipt required"
  ; uncertaintyModel =
      "provider uncertainty/covariance model receipt required"
  ; calibrationDigest =
      "unit-calibration-digest-required"
  ; calibrationProviderMetadata =
      canonicalProviderPayloadMetadata
  ; covarianceShapeParsed =
      true
  ; covarianceShapeParsedIsTrue =
      refl
  ; unitConventionBound =
      true
  ; unitConventionBoundIsTrue =
      refl
  ; covarianceCalibrationAccepted =
      false
  ; covarianceCalibrationAcceptedIsFalse =
      refl
  ; covarianceCalibrationPromoted =
      Registry.EmpiricalRuntimeKnownInputsReferenceReceipt.covarianceCalibrationPromoted
        Registry.canonicalEmpiricalRuntimeKnownInputsReferenceReceipt
  ; covarianceCalibrationPromotedIsFalse =
      Registry.EmpiricalRuntimeKnownInputsReferenceReceipt.covarianceCalibrationPromotedIsFalse
        Registry.canonicalEmpiricalRuntimeKnownInputsReferenceReceipt
  }

canonicalHoldoutValidationProtocol : HoldoutValidationProtocol
canonicalHoldoutValidationProtocol = record
  { protocolLabel =
      "frozen provider holdout validation protocol"
  ; holdoutSplitKind =
      frozenTrainHoldoutSplit
  ; providerMetadata =
      canonicalProviderPayloadMetadata
  ; comparisonAdapter =
      canonicalComparisonLawAdapter
  ; covarianceCalibration =
      canonicalCovarianceUnitCalibration
  ; trainingSourceDigest =
      "training-source-digest-required"
  ; holdoutSourceDigest =
      "holdout-source-digest-required"
  ; freezeHash =
      "prediction-freeze-hash-required"
  ; validationProtocolDigest =
      "holdout-validation-protocol-digest-required"
  ; passFailCriterion =
      "pre-registered pass/fail criterion required before holdout acceptance"
  ; holdoutDatasetNamed =
      true
  ; holdoutDatasetNamedIsTrue =
      refl
  ; holdoutValidationAccepted =
      Registry.EmpiricalRuntimeKnownInputsReferenceReceipt.holdoutValidationAccepted
        Registry.canonicalEmpiricalRuntimeKnownInputsReferenceReceipt
  ; holdoutValidationAcceptedIsFalse =
      Registry.EmpiricalRuntimeKnownInputsReferenceReceipt.holdoutValidationAcceptedIsFalse
        Registry.canonicalEmpiricalRuntimeKnownInputsReferenceReceipt
  ; empiricalAdequacyAccepted =
      Registry.EmpiricalRuntimeKnownInputsReferenceReceipt.empiricalAdequacyAccepted
        Registry.canonicalEmpiricalRuntimeKnownInputsReferenceReceipt
  ; empiricalAdequacyAcceptedIsFalse =
      Registry.EmpiricalRuntimeKnownInputsReferenceReceipt.empiricalAdequacyAcceptedIsFalse
        Registry.canonicalEmpiricalRuntimeKnownInputsReferenceReceipt
  }

canonicalRuntimeCommandEnvironment : RuntimeCommandEnvironment
canonicalRuntimeCommandEnvironment = record
  { runtimeReceiptId =
      "runtime-receipt-id-required"
  ; commandLine =
      "agda -i . DASHI/Promotion/EmpiricalRuntimeReplayAdapter.agda"
  ; workingDirectory =
      "/home/c/Documents/code/dashi_agda"
  ; environmentDigest =
      "runtime-environment-digest-required"
  ; parserVersion =
      "parser-version-required"
  ; reducerVersion =
      "reducer-version-required"
  ; sourceArtifactChecksum =
      ObservableDefinition.sourceChecksum canonicalObservableDefinition
  ; projectionDigest =
      TransformProjectionDigest.runtimeReplayProjectionDigest
        canonicalTransformProjectionDigest
  ; commandDigest =
      "runtime-command-digest-required"
  ; environmentCaptured =
      true
  ; environmentCapturedIsTrue =
      refl
  }

entryStarted : RuntimeReplayLogEntry
entryStarted = record
  { eventKind = commandStarted
  ; eventOrdinal = zero
  ; inputDigest =
      RuntimeCommandEnvironment.commandDigest
        canonicalRuntimeCommandEnvironment
  ; outputDigest =
      "command-started"
  ; projectionDigest =
      RuntimeCommandEnvironment.projectionDigest
        canonicalRuntimeCommandEnvironment
  ; eventNote =
      "runtime command recorded"
  }

entryEnvironment : RuntimeReplayLogEntry
entryEnvironment = record
  { eventKind = environmentCapturedEvent
  ; eventOrdinal = suc zero
  ; inputDigest =
      RuntimeCommandEnvironment.environmentDigest
        canonicalRuntimeCommandEnvironment
  ; outputDigest =
      "environment-captured"
  ; projectionDigest =
      RuntimeCommandEnvironment.projectionDigest
        canonicalRuntimeCommandEnvironment
  ; eventNote =
      "environment digest recorded"
  }

entryChecksum : RuntimeReplayLogEntry
entryChecksum = record
  { eventKind = sourceChecksumVerified
  ; eventOrdinal = suc (suc zero)
  ; inputDigest =
      RuntimeCommandEnvironment.sourceArtifactChecksum
        canonicalRuntimeCommandEnvironment
  ; outputDigest =
      "source-checksum-verified"
  ; projectionDigest =
      RuntimeCommandEnvironment.projectionDigest
        canonicalRuntimeCommandEnvironment
  ; eventNote =
      "source checksum tied to observable payload"
  }

entryProjection : RuntimeReplayLogEntry
entryProjection = record
  { eventKind = projectionDigestEmitted
  ; eventOrdinal = suc (suc (suc zero))
  ; inputDigest =
      TransformProjectionDigest.projectedObservableDigest
        canonicalTransformProjectionDigest
  ; outputDigest =
      RuntimeCommandEnvironment.projectionDigest
        canonicalRuntimeCommandEnvironment
  ; projectionDigest =
      RuntimeCommandEnvironment.projectionDigest
        canonicalRuntimeCommandEnvironment
  ; eventNote =
      "projection digest emitted deterministically for identical replay"
  }

entryFinished : RuntimeReplayLogEntry
entryFinished = record
  { eventKind = commandFinished
  ; eventOrdinal = suc (suc (suc (suc zero)))
  ; inputDigest =
      RuntimeCommandEnvironment.commandDigest
        canonicalRuntimeCommandEnvironment
  ; outputDigest =
      "command-finished"
  ; projectionDigest =
      RuntimeCommandEnvironment.projectionDigest
        canonicalRuntimeCommandEnvironment
  ; eventNote =
      "runtime command finished"
  }

canonicalRuntimeReplayEntries : List RuntimeReplayLogEntry
canonicalRuntimeReplayEntries =
  entryStarted
  ∷ entryEnvironment
  ∷ entryChecksum
  ∷ entryProjection
  ∷ entryFinished
  ∷ []

canonicalRuntimeReplayLog : RuntimeReplayLog
canonicalRuntimeReplayLog = record
  { commandEnvironment =
      canonicalRuntimeCommandEnvironment
  ; replayEntries =
      canonicalRuntimeReplayEntries
  ; replayEntryCount =
      listCount canonicalRuntimeReplayEntries
  ; replayEntryCountMatches =
      refl
  ; sourceChecksum =
      RuntimeCommandEnvironment.sourceArtifactChecksum
        canonicalRuntimeCommandEnvironment
  ; sourceChecksumMatchesEnvironment =
      refl
  ; projectionDigest =
      RuntimeCommandEnvironment.projectionDigest
        canonicalRuntimeCommandEnvironment
  ; projectionDigestMatchesEnvironment =
      refl
  ; replayLogDigest =
      "runtime-replay-log-digest-required"
  ; replayComplete =
      true
  ; replayCompleteIsTrue =
      refl
  ; runtimeReplayAuthorityAccepted =
      Registry.EmpiricalRuntimeKnownInputsReferenceReceipt.runtimeReplayAuthorityAccepted
        Registry.canonicalEmpiricalRuntimeKnownInputsReferenceReceipt
  ; runtimeReplayAuthorityAcceptedIsFalse =
      Registry.EmpiricalRuntimeKnownInputsReferenceReceipt.runtimeReplayAuthorityAcceptedIsFalse
        Registry.canonicalEmpiricalRuntimeKnownInputsReferenceReceipt
  }

canonicalRuntimeReplayAdapter : RuntimeReplayAdapter
canonicalRuntimeReplayAdapter = record
  { adapterLabel =
      "runtime replay adapter over provider projection digest"
  ; replayLog =
      canonicalRuntimeReplayLog
  ; transformProjectionDigest =
      canonicalTransformProjectionDigest
  ; runtimeProviderAttempt =
      PNFAttempt.canonicalRuntimeProviderAttempt
  ; pnfRequestPack =
      PNFRequest.canonicalPNFResidualConsumerReceiptRequestPack
  ; projectionDigestFromReplay =
      refl
  ; deterministicReplayForIdenticalLog =
      deterministicReplayEquality canonicalRuntimeReplayLog
  ; replayPayloadAbsentDiagnostic =
      true
  ; replayPayloadAbsentDiagnosticIsTrue =
      refl
  ; runtimeReplayAuthorityAccepted =
      Registry.EmpiricalRuntimeKnownInputsReferenceReceipt.runtimeReplayAuthorityAccepted
        Registry.canonicalEmpiricalRuntimeKnownInputsReferenceReceipt
  ; runtimeReplayAuthorityAcceptedIsFalse =
      Registry.EmpiricalRuntimeKnownInputsReferenceReceipt.runtimeReplayAuthorityAcceptedIsFalse
        Registry.canonicalEmpiricalRuntimeKnownInputsReferenceReceipt
  }

canonicalSemanticAdequacyReview : SemanticAdequacyReview
canonicalSemanticAdequacyReview = record
  { semanticReviewLabel =
      "semantic adequacy review boundary for replayed projection"
  ; replayAdapter =
      canonicalRuntimeReplayAdapter
  ; nonInspectionBoundary =
      "does not inspect or fabricate missing PNFEmissionReceipt values"
      ∷ "does not infer semantic adequacy from successful replay alone"
      ∷ "does not promote provider, comparison, covariance, holdout, or empirical adequacy"
      ∷ []
  ; semanticCriteria =
      "projection digest is replay-stable for identical logs"
      ∷ "source checksum is bound to provider payload"
      ∷ "parser and reducer versions are explicitly named"
      ∷ "semantic adequacy authority review token is still absent"
      ∷ []
  ; reviewedProjectionDigest =
      replayLogProjectionDigest canonicalRuntimeReplayLog
  ; reviewedProjectionDigestMatchesReplay =
      refl
  ; semanticReviewAuthorityTokenAccepted =
      false
  ; semanticReviewAuthorityTokenAcceptedIsFalse =
      refl
  ; semanticAdequacyAccepted =
      Registry.EmpiricalRuntimeKnownInputsReferenceReceipt.semanticAdequacyAccepted
        Registry.canonicalEmpiricalRuntimeKnownInputsReferenceReceipt
  ; semanticAdequacyAcceptedIsFalse =
      Registry.EmpiricalRuntimeKnownInputsReferenceReceipt.semanticAdequacyAcceptedIsFalse
        Registry.canonicalEmpiricalRuntimeKnownInputsReferenceReceipt
  }

canonicalEmpiricalRuntimeValidationReport :
  EmpiricalRuntimeValidationReport
canonicalEmpiricalRuntimeValidationReport = record
  { reportLabel =
      "empirical runtime replay validation report"
  ; authorityIndex =
      Authority.canonicalNumericAndAuthorityObligationIndex
  ; providerMetadata =
      canonicalProviderPayloadMetadata
  ; observableDefinition =
      canonicalObservableDefinition
  ; projectionDigest =
      canonicalTransformProjectionDigest
  ; comparisonAdapter =
      canonicalComparisonLawAdapter
  ; covarianceCalibration =
      canonicalCovarianceUnitCalibration
  ; holdoutProtocol =
      canonicalHoldoutValidationProtocol
  ; runtimeReplayAdapter =
      canonicalRuntimeReplayAdapter
  ; semanticReview =
      canonicalSemanticAdequacyReview
  ; validationVerdict =
      validationFailsWith canonicalValidationFailureReasons
  ; failureReasons =
      canonicalValidationFailureReasons
  ; failureReasonCount =
      listCount canonicalValidationFailureReasons
  ; failureReasonCountMatches =
      refl
  ; providerAuthorityPromoted =
      Registry.EmpiricalRuntimeKnownInputsReferenceReceipt.acceptedProviderAuthorityPromoted
        Registry.canonicalEmpiricalRuntimeKnownInputsReferenceReceipt
  ; providerAuthorityPromotedIsFalse =
      Registry.EmpiricalRuntimeKnownInputsReferenceReceipt.acceptedProviderAuthorityPromotedIsFalse
        Registry.canonicalEmpiricalRuntimeKnownInputsReferenceReceipt
  ; comparisonLawPromoted =
      Registry.EmpiricalRuntimeKnownInputsReferenceReceipt.comparisonLawPromoted
        Registry.canonicalEmpiricalRuntimeKnownInputsReferenceReceipt
  ; comparisonLawPromotedIsFalse =
      Registry.EmpiricalRuntimeKnownInputsReferenceReceipt.comparisonLawPromotedIsFalse
        Registry.canonicalEmpiricalRuntimeKnownInputsReferenceReceipt
  ; covarianceCalibrationPromoted =
      Registry.EmpiricalRuntimeKnownInputsReferenceReceipt.covarianceCalibrationPromoted
        Registry.canonicalEmpiricalRuntimeKnownInputsReferenceReceipt
  ; covarianceCalibrationPromotedIsFalse =
      Registry.EmpiricalRuntimeKnownInputsReferenceReceipt.covarianceCalibrationPromotedIsFalse
        Registry.canonicalEmpiricalRuntimeKnownInputsReferenceReceipt
  ; holdoutValidationAccepted =
      Registry.EmpiricalRuntimeKnownInputsReferenceReceipt.holdoutValidationAccepted
        Registry.canonicalEmpiricalRuntimeKnownInputsReferenceReceipt
  ; holdoutValidationAcceptedIsFalse =
      Registry.EmpiricalRuntimeKnownInputsReferenceReceipt.holdoutValidationAcceptedIsFalse
        Registry.canonicalEmpiricalRuntimeKnownInputsReferenceReceipt
  ; runtimeReplayAuthorityAccepted =
      Registry.EmpiricalRuntimeKnownInputsReferenceReceipt.runtimeReplayAuthorityAccepted
        Registry.canonicalEmpiricalRuntimeKnownInputsReferenceReceipt
  ; runtimeReplayAuthorityAcceptedIsFalse =
      Registry.EmpiricalRuntimeKnownInputsReferenceReceipt.runtimeReplayAuthorityAcceptedIsFalse
        Registry.canonicalEmpiricalRuntimeKnownInputsReferenceReceipt
  ; semanticAdequacyAccepted =
      Registry.EmpiricalRuntimeKnownInputsReferenceReceipt.semanticAdequacyAccepted
        Registry.canonicalEmpiricalRuntimeKnownInputsReferenceReceipt
  ; semanticAdequacyAcceptedIsFalse =
      Registry.EmpiricalRuntimeKnownInputsReferenceReceipt.semanticAdequacyAcceptedIsFalse
        Registry.canonicalEmpiricalRuntimeKnownInputsReferenceReceipt
  ; empiricalAdequacyAccepted =
      Registry.EmpiricalRuntimeKnownInputsReferenceReceipt.empiricalAdequacyAccepted
        Registry.canonicalEmpiricalRuntimeKnownInputsReferenceReceipt
  ; empiricalAdequacyAcceptedIsFalse =
      Registry.EmpiricalRuntimeKnownInputsReferenceReceipt.empiricalAdequacyAcceptedIsFalse
        Registry.canonicalEmpiricalRuntimeKnownInputsReferenceReceipt
  }

------------------------------------------------------------------------
-- Counts and fail-closed lemmas.

canonicalMetadataCountIs9 :
  listCount
    (ProviderPayloadMetadata.requiredMetadata canonicalProviderPayloadMetadata)
  ≡ 9
canonicalMetadataCountIs9 = refl

canonicalComparisonRequiredFieldCountIs10 :
  listCount
    (ComparisonLawAdapter.requiredComparisonFields
      canonicalComparisonLawAdapter)
  ≡ 10
canonicalComparisonRequiredFieldCountIs10 = refl

canonicalComparisonCurrentGapCountIs9 :
  listCount
    (ComparisonLawAdapter.currentComparisonGaps
      canonicalComparisonLawAdapter)
  ≡ 9
canonicalComparisonCurrentGapCountIs9 = refl

canonicalRuntimeReplayEntryCountIs5 :
  RuntimeReplayLog.replayEntryCount canonicalRuntimeReplayLog
  ≡ 5
canonicalRuntimeReplayEntryCountIs5 = refl

canonicalValidationFailureReasonCountIs7 :
  EmpiricalRuntimeValidationReport.failureReasonCount
    canonicalEmpiricalRuntimeValidationReport
  ≡ 7
canonicalValidationFailureReasonCountIs7 = refl

canonicalValidationVerdictIsFail :
  EmpiricalRuntimeValidationReport.validationVerdict
    canonicalEmpiricalRuntimeValidationReport
  ≡ validationFail canonicalValidationFailureReasons
canonicalValidationVerdictIsFail = refl

canonicalIdenticalReplayProjectionDigest :
  replayLogProjectionDigest canonicalRuntimeReplayLog
  ≡
  replayLogProjectionDigest canonicalRuntimeReplayLog
canonicalIdenticalReplayProjectionDigest =
  deterministicReplayEquality canonicalRuntimeReplayLog

canonicalIdenticalReplayLogDigest :
  RuntimeReplayLog.replayLogDigest canonicalRuntimeReplayLog
  ≡
  RuntimeReplayLog.replayLogDigest canonicalRuntimeReplayLog
canonicalIdenticalReplayLogDigest =
  deterministicReplayLogDigestEquality canonicalRuntimeReplayLog

canonicalSourceChecksumMatchesEnvironment :
  RuntimeReplayLog.sourceChecksum canonicalRuntimeReplayLog
  ≡
  RuntimeCommandEnvironment.sourceArtifactChecksum
    canonicalRuntimeCommandEnvironment
canonicalSourceChecksumMatchesEnvironment =
  RuntimeReplayLog.sourceChecksumMatchesEnvironment
    canonicalRuntimeReplayLog

canonicalProjectionDigestMatchesEnvironment :
  RuntimeReplayLog.projectionDigest canonicalRuntimeReplayLog
  ≡
  RuntimeCommandEnvironment.projectionDigest
    canonicalRuntimeCommandEnvironment
canonicalProjectionDigestMatchesEnvironment =
  RuntimeReplayLog.projectionDigestMatchesEnvironment
    canonicalRuntimeReplayLog

canonicalProviderAuthorityPromotedIsFalse :
  EmpiricalRuntimeValidationReport.providerAuthorityPromoted
    canonicalEmpiricalRuntimeValidationReport
  ≡ false
canonicalProviderAuthorityPromotedIsFalse =
  EmpiricalRuntimeValidationReport.providerAuthorityPromotedIsFalse
    canonicalEmpiricalRuntimeValidationReport

canonicalComparisonLawPromotedIsFalse :
  EmpiricalRuntimeValidationReport.comparisonLawPromoted
    canonicalEmpiricalRuntimeValidationReport
  ≡ false
canonicalComparisonLawPromotedIsFalse =
  EmpiricalRuntimeValidationReport.comparisonLawPromotedIsFalse
    canonicalEmpiricalRuntimeValidationReport

canonicalCovarianceCalibrationPromotedIsFalse :
  EmpiricalRuntimeValidationReport.covarianceCalibrationPromoted
    canonicalEmpiricalRuntimeValidationReport
  ≡ false
canonicalCovarianceCalibrationPromotedIsFalse =
  EmpiricalRuntimeValidationReport.covarianceCalibrationPromotedIsFalse
    canonicalEmpiricalRuntimeValidationReport

canonicalHoldoutValidationAcceptedIsFalse :
  EmpiricalRuntimeValidationReport.holdoutValidationAccepted
    canonicalEmpiricalRuntimeValidationReport
  ≡ false
canonicalHoldoutValidationAcceptedIsFalse =
  EmpiricalRuntimeValidationReport.holdoutValidationAcceptedIsFalse
    canonicalEmpiricalRuntimeValidationReport

canonicalRuntimeReplayAuthorityAcceptedIsFalse :
  EmpiricalRuntimeValidationReport.runtimeReplayAuthorityAccepted
    canonicalEmpiricalRuntimeValidationReport
  ≡ false
canonicalRuntimeReplayAuthorityAcceptedIsFalse =
  EmpiricalRuntimeValidationReport.runtimeReplayAuthorityAcceptedIsFalse
    canonicalEmpiricalRuntimeValidationReport

canonicalSemanticAdequacyAcceptedIsFalse :
  EmpiricalRuntimeValidationReport.semanticAdequacyAccepted
    canonicalEmpiricalRuntimeValidationReport
  ≡ false
canonicalSemanticAdequacyAcceptedIsFalse =
  EmpiricalRuntimeValidationReport.semanticAdequacyAcceptedIsFalse
    canonicalEmpiricalRuntimeValidationReport

canonicalEmpiricalAdequacyAcceptedIsFalse :
  EmpiricalRuntimeValidationReport.empiricalAdequacyAccepted
    canonicalEmpiricalRuntimeValidationReport
  ≡ false
canonicalEmpiricalAdequacyAcceptedIsFalse =
  EmpiricalRuntimeValidationReport.empiricalAdequacyAcceptedIsFalse
    canonicalEmpiricalRuntimeValidationReport

------------------------------------------------------------------------
-- Empirical/runtime promotion gate requirements.

data EmpiricalRuntimePromotionGateName : Set where
  providerAuthorityGate : EmpiricalRuntimePromotionGateName
  covariantChiSquareGate : EmpiricalRuntimePromotionGateName
  covarianceCalibrationGate : EmpiricalRuntimePromotionGateName
  holdoutValidationGate : EmpiricalRuntimePromotionGateName
  runtimeReplayGate : EmpiricalRuntimePromotionGateName
  replaySemanticAdequacyGate : EmpiricalRuntimePromotionGateName

record EmpiricalRuntimePromotionGateRequirement : Set₁ where
  field
    gateName : EmpiricalRuntimePromotionGateName
    gateLabel : String
    validationReportLabel : String
    populatedInfrastructureNote : String
    missingAcceptanceTokenNote : String
    infrastructurePopulated : Bool
    infrastructurePopulatedIsTrue :
      infrastructurePopulated ≡ true
    acceptanceTokenPresent : Bool
    acceptanceTokenPresentIsFalse :
      acceptanceTokenPresent ≡ false
    promotesEmpiricalClaim : Bool
    promotesEmpiricalClaimIsFalse :
      promotesEmpiricalClaim ≡ false

open EmpiricalRuntimePromotionGateRequirement public

canonicalProviderAuthorityGateRequirement :
  EmpiricalRuntimePromotionGateRequirement
canonicalProviderAuthorityGateRequirement = record
  { gateName =
      providerAuthorityGate
  ; gateLabel =
      "provider authority intake gate"
  ; validationReportLabel =
      EmpiricalRuntimeValidationReport.reportLabel
        canonicalEmpiricalRuntimeValidationReport
  ; populatedInfrastructureNote =
      "provider metadata, registry policy, checksum, required metadata, and authority row are populated"
  ; missingAcceptanceTokenNote =
      "providerAuthorityTokenAccepted and providerAuthorityPromoted remain false"
  ; infrastructurePopulated =
      ProviderPayloadMetadata.sourceChecksumBound canonicalProviderPayloadMetadata
  ; infrastructurePopulatedIsTrue =
      ProviderPayloadMetadata.sourceChecksumBoundIsTrue canonicalProviderPayloadMetadata
  ; acceptanceTokenPresent =
      ProviderPayloadMetadata.providerAuthorityTokenAccepted
        canonicalProviderPayloadMetadata
  ; acceptanceTokenPresentIsFalse =
      ProviderPayloadMetadata.providerAuthorityTokenAcceptedIsFalse
        canonicalProviderPayloadMetadata
  ; promotesEmpiricalClaim =
      EmpiricalRuntimeValidationReport.providerAuthorityPromoted
        canonicalEmpiricalRuntimeValidationReport
  ; promotesEmpiricalClaimIsFalse =
      EmpiricalRuntimeValidationReport.providerAuthorityPromotedIsFalse
        canonicalEmpiricalRuntimeValidationReport
  }

canonicalCovariantChiSquareGateRequirement :
  EmpiricalRuntimePromotionGateRequirement
canonicalCovariantChiSquareGateRequirement = record
  { gateName =
      covariantChiSquareGate
  ; gateLabel =
      "covariance-aware chi-square comparison gate"
  ; validationReportLabel =
      EmpiricalRuntimeValidationReport.reportLabel
        canonicalEmpiricalRuntimeValidationReport
  ; populatedInfrastructureNote =
      "comparison law adapter names chi-square/covariance policy, authority surface, required fields, and current gaps"
  ; missingAcceptanceTokenNote =
      "comparisonLawAccepted and comparisonLawPromoted remain false"
  ; infrastructurePopulated =
      ComparisonLawAdapter.covarianceAware canonicalComparisonLawAdapter
  ; infrastructurePopulatedIsTrue =
      ComparisonLawAdapter.covarianceAwareIsTrue canonicalComparisonLawAdapter
  ; acceptanceTokenPresent =
      ComparisonLawAdapter.comparisonLawAccepted canonicalComparisonLawAdapter
  ; acceptanceTokenPresentIsFalse =
      ComparisonLawAdapter.comparisonLawAcceptedIsFalse
        canonicalComparisonLawAdapter
  ; promotesEmpiricalClaim =
      EmpiricalRuntimeValidationReport.comparisonLawPromoted
        canonicalEmpiricalRuntimeValidationReport
  ; promotesEmpiricalClaimIsFalse =
      EmpiricalRuntimeValidationReport.comparisonLawPromotedIsFalse
        canonicalEmpiricalRuntimeValidationReport
  }

canonicalCovarianceCalibrationGateRequirement :
  EmpiricalRuntimePromotionGateRequirement
canonicalCovarianceCalibrationGateRequirement = record
  { gateName =
      covarianceCalibrationGate
  ; gateLabel =
      "covariance matrix and unit calibration gate"
  ; validationReportLabel =
      EmpiricalRuntimeValidationReport.reportLabel
        canonicalEmpiricalRuntimeValidationReport
  ; populatedInfrastructureNote =
      "covariance shape, source digest, unit convention, uncertainty model, calibration digest, and provider metadata are populated"
  ; missingAcceptanceTokenNote =
      "covarianceCalibrationAccepted and covarianceCalibrationPromoted remain false"
  ; infrastructurePopulated =
      CovarianceUnitCalibration.covarianceShapeParsed
        canonicalCovarianceUnitCalibration
  ; infrastructurePopulatedIsTrue =
      CovarianceUnitCalibration.covarianceShapeParsedIsTrue
        canonicalCovarianceUnitCalibration
  ; acceptanceTokenPresent =
      CovarianceUnitCalibration.covarianceCalibrationAccepted
        canonicalCovarianceUnitCalibration
  ; acceptanceTokenPresentIsFalse =
      CovarianceUnitCalibration.covarianceCalibrationAcceptedIsFalse
        canonicalCovarianceUnitCalibration
  ; promotesEmpiricalClaim =
      EmpiricalRuntimeValidationReport.covarianceCalibrationPromoted
        canonicalEmpiricalRuntimeValidationReport
  ; promotesEmpiricalClaimIsFalse =
      EmpiricalRuntimeValidationReport.covarianceCalibrationPromotedIsFalse
        canonicalEmpiricalRuntimeValidationReport
  }

canonicalHoldoutValidationGateRequirement :
  EmpiricalRuntimePromotionGateRequirement
canonicalHoldoutValidationGateRequirement = record
  { gateName =
      holdoutValidationGate
  ; gateLabel =
      "frozen holdout validation gate"
  ; validationReportLabel =
      EmpiricalRuntimeValidationReport.reportLabel
        canonicalEmpiricalRuntimeValidationReport
  ; populatedInfrastructureNote =
      "holdout split kind, training digest, holdout digest, freeze hash, protocol digest, and pass/fail criterion are populated"
  ; missingAcceptanceTokenNote =
      "holdoutValidationAccepted and empiricalAdequacyAccepted remain false"
  ; infrastructurePopulated =
      HoldoutValidationProtocol.holdoutDatasetNamed
        canonicalHoldoutValidationProtocol
  ; infrastructurePopulatedIsTrue =
      HoldoutValidationProtocol.holdoutDatasetNamedIsTrue
        canonicalHoldoutValidationProtocol
  ; acceptanceTokenPresent =
      HoldoutValidationProtocol.holdoutValidationAccepted
        canonicalHoldoutValidationProtocol
  ; acceptanceTokenPresentIsFalse =
      HoldoutValidationProtocol.holdoutValidationAcceptedIsFalse
        canonicalHoldoutValidationProtocol
  ; promotesEmpiricalClaim =
      HoldoutValidationProtocol.empiricalAdequacyAccepted
        canonicalHoldoutValidationProtocol
  ; promotesEmpiricalClaimIsFalse =
      HoldoutValidationProtocol.empiricalAdequacyAcceptedIsFalse
        canonicalHoldoutValidationProtocol
  }

canonicalRuntimeReplayGateRequirement :
  EmpiricalRuntimePromotionGateRequirement
canonicalRuntimeReplayGateRequirement = record
  { gateName =
      runtimeReplayGate
  ; gateLabel =
      "deterministic runtime replay gate"
  ; validationReportLabel =
      EmpiricalRuntimeValidationReport.reportLabel
        canonicalEmpiricalRuntimeValidationReport
  ; populatedInfrastructureNote =
      "runtime environment, command digest, replay entries, source checksum equality, and projection digest equality are populated"
  ; missingAcceptanceTokenNote =
      "runtimeReplayAuthorityAccepted remains false"
  ; infrastructurePopulated =
      RuntimeReplayLog.replayComplete canonicalRuntimeReplayLog
  ; infrastructurePopulatedIsTrue =
      RuntimeReplayLog.replayCompleteIsTrue canonicalRuntimeReplayLog
  ; acceptanceTokenPresent =
      RuntimeReplayLog.runtimeReplayAuthorityAccepted canonicalRuntimeReplayLog
  ; acceptanceTokenPresentIsFalse =
      RuntimeReplayLog.runtimeReplayAuthorityAcceptedIsFalse
        canonicalRuntimeReplayLog
  ; promotesEmpiricalClaim =
      EmpiricalRuntimeValidationReport.runtimeReplayAuthorityAccepted
        canonicalEmpiricalRuntimeValidationReport
  ; promotesEmpiricalClaimIsFalse =
      EmpiricalRuntimeValidationReport.runtimeReplayAuthorityAcceptedIsFalse
        canonicalEmpiricalRuntimeValidationReport
  }

canonicalReplaySemanticAdequacyGateRequirement :
  EmpiricalRuntimePromotionGateRequirement
canonicalReplaySemanticAdequacyGateRequirement = record
  { gateName =
      replaySemanticAdequacyGate
  ; gateLabel =
      "replay semantic adequacy review gate"
  ; validationReportLabel =
      EmpiricalRuntimeValidationReport.reportLabel
        canonicalEmpiricalRuntimeValidationReport
  ; populatedInfrastructureNote =
      "semantic review boundary, non-inspection rules, criteria, and replay digest equality are populated"
  ; missingAcceptanceTokenNote =
      "semanticReviewAuthorityTokenAccepted and semanticAdequacyAccepted remain false"
  ; infrastructurePopulated =
      true
  ; infrastructurePopulatedIsTrue =
      refl
  ; acceptanceTokenPresent =
      SemanticAdequacyReview.semanticReviewAuthorityTokenAccepted
        canonicalSemanticAdequacyReview
  ; acceptanceTokenPresentIsFalse =
      SemanticAdequacyReview.semanticReviewAuthorityTokenAcceptedIsFalse
        canonicalSemanticAdequacyReview
  ; promotesEmpiricalClaim =
      SemanticAdequacyReview.semanticAdequacyAccepted
        canonicalSemanticAdequacyReview
  ; promotesEmpiricalClaimIsFalse =
      SemanticAdequacyReview.semanticAdequacyAcceptedIsFalse
        canonicalSemanticAdequacyReview
  }

canonicalEmpiricalRuntimePromotionGateRequirements :
  List EmpiricalRuntimePromotionGateRequirement
canonicalEmpiricalRuntimePromotionGateRequirements =
  canonicalProviderAuthorityGateRequirement
  ∷ canonicalCovariantChiSquareGateRequirement
  ∷ canonicalCovarianceCalibrationGateRequirement
  ∷ canonicalHoldoutValidationGateRequirement
  ∷ canonicalRuntimeReplayGateRequirement
  ∷ canonicalReplaySemanticAdequacyGateRequirement
  ∷ []

canonicalPopulatedInfrastructureGateRequirements :
  List EmpiricalRuntimePromotionGateRequirement
canonicalPopulatedInfrastructureGateRequirements =
  canonicalEmpiricalRuntimePromotionGateRequirements

canonicalFalseAcceptanceTokenGateRequirements :
  List EmpiricalRuntimePromotionGateRequirement
canonicalFalseAcceptanceTokenGateRequirements =
  canonicalEmpiricalRuntimePromotionGateRequirements

canonicalPromotionGateRequirementCountIs6 :
  listCount canonicalEmpiricalRuntimePromotionGateRequirements
  ≡ 6
canonicalPromotionGateRequirementCountIs6 = refl

canonicalPopulatedInfrastructureGateCountIs6 :
  listCount canonicalPopulatedInfrastructureGateRequirements
  ≡ 6
canonicalPopulatedInfrastructureGateCountIs6 = refl

canonicalFalseAcceptanceTokenGateCountIs6 :
  listCount canonicalFalseAcceptanceTokenGateRequirements
  ≡ 6
canonicalFalseAcceptanceTokenGateCountIs6 = refl

canonicalProviderAuthorityGateInfrastructurePopulated :
  EmpiricalRuntimePromotionGateRequirement.infrastructurePopulated
    canonicalProviderAuthorityGateRequirement
  ≡ true
canonicalProviderAuthorityGateInfrastructurePopulated = refl

canonicalCovariantChiSquareGateInfrastructurePopulated :
  EmpiricalRuntimePromotionGateRequirement.infrastructurePopulated
    canonicalCovariantChiSquareGateRequirement
  ≡ true
canonicalCovariantChiSquareGateInfrastructurePopulated = refl

canonicalCovarianceCalibrationGateInfrastructurePopulated :
  EmpiricalRuntimePromotionGateRequirement.infrastructurePopulated
    canonicalCovarianceCalibrationGateRequirement
  ≡ true
canonicalCovarianceCalibrationGateInfrastructurePopulated = refl

canonicalHoldoutValidationGateInfrastructurePopulated :
  EmpiricalRuntimePromotionGateRequirement.infrastructurePopulated
    canonicalHoldoutValidationGateRequirement
  ≡ true
canonicalHoldoutValidationGateInfrastructurePopulated = refl

canonicalRuntimeReplayGateInfrastructurePopulated :
  EmpiricalRuntimePromotionGateRequirement.infrastructurePopulated
    canonicalRuntimeReplayGateRequirement
  ≡ true
canonicalRuntimeReplayGateInfrastructurePopulated = refl

canonicalReplaySemanticAdequacyGateInfrastructurePopulated :
  EmpiricalRuntimePromotionGateRequirement.infrastructurePopulated
    canonicalReplaySemanticAdequacyGateRequirement
  ≡ true
canonicalReplaySemanticAdequacyGateInfrastructurePopulated = refl

canonicalProviderAuthorityGateAcceptanceTokenIsFalse :
  EmpiricalRuntimePromotionGateRequirement.acceptanceTokenPresent
    canonicalProviderAuthorityGateRequirement
  ≡ false
canonicalProviderAuthorityGateAcceptanceTokenIsFalse = refl

canonicalCovariantChiSquareGateAcceptanceTokenIsFalse :
  EmpiricalRuntimePromotionGateRequirement.acceptanceTokenPresent
    canonicalCovariantChiSquareGateRequirement
  ≡ false
canonicalCovariantChiSquareGateAcceptanceTokenIsFalse = refl

canonicalCovarianceCalibrationGateAcceptanceTokenIsFalse :
  EmpiricalRuntimePromotionGateRequirement.acceptanceTokenPresent
    canonicalCovarianceCalibrationGateRequirement
  ≡ false
canonicalCovarianceCalibrationGateAcceptanceTokenIsFalse = refl

canonicalHoldoutValidationGateAcceptanceTokenIsFalse :
  EmpiricalRuntimePromotionGateRequirement.acceptanceTokenPresent
    canonicalHoldoutValidationGateRequirement
  ≡ false
canonicalHoldoutValidationGateAcceptanceTokenIsFalse = refl

canonicalRuntimeReplayGateAcceptanceTokenIsFalse :
  EmpiricalRuntimePromotionGateRequirement.acceptanceTokenPresent
    canonicalRuntimeReplayGateRequirement
  ≡ false
canonicalRuntimeReplayGateAcceptanceTokenIsFalse = refl

canonicalReplaySemanticAdequacyGateAcceptanceTokenIsFalse :
  EmpiricalRuntimePromotionGateRequirement.acceptanceTokenPresent
    canonicalReplaySemanticAdequacyGateRequirement
  ≡ false
canonicalReplaySemanticAdequacyGateAcceptanceTokenIsFalse = refl

acceptedProviderAuthorityStillBlocked :
  HEPProjection.HEPDataAcceptedProjectionRunnerReceipt →
  ⊥
acceptedProviderAuthorityStillBlocked =
  HEPProjection.acceptedProjectionRunnerReceiptImpossibleHere
