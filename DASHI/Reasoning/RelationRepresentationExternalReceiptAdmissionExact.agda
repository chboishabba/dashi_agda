module DASHI.Reasoning.RelationRepresentationExternalReceiptAdmissionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.RelationRepresentationStudyValidationObligationsExact as Study
import DASHI.Reasoning.RelationRepresentationTOEInferenceHandoffExact as TOE

------------------------------------------------------------------------
-- EXTERNAL RECEIPT ADMISSION
--
-- Purpose:
--   turn an external empirical payload into a typed candidate receipt without
--   pretending that the payload has already been checked, reproduced, or
--   promoted into Stage-6/Stage-7 inference.
--
-- This is intentionally one layer below the future #636 owners. Once the
-- Stage-6/7 experiment architecture is merged, a checked receipt can be fed to
-- PredictionEnvelopeExact / CalibratedExperimentInferenceExact /
-- RobustExperimentInferenceFrontierExact through a thin adapter.
------------------------------------------------------------------------

record ArtifactPointer : Set where
  constructor artifactPointer
  field
    artifact : Study.ValidationArtifact
    location : String
    contentHash : String
    producerRevision : String

open ArtifactPointer public

record ExternalStudyReceipt : Set where
  constructor externalStudyReceipt
  field
    profile : Study.StudyValidationProfile
    receiptSchemaVersion : String
    modelOrSystemIdentity : String
    payloadPointers : List ArtifactPointer
    environmentDigest : String
    admissionNote : String

open ExternalStudyReceipt public

record ReceiptPackageCheck (receipt : ExternalStudyReceipt) : Set where
  constructor receiptPackageCheck
  field
    schemaRecognized : Bool
    referencedPayloadsResolve : Bool
    hashesMatch : Bool
    modelRevisionPinned : Bool
    codeRevisionPinned : Bool
    environmentPinned : Bool
    requiredArtifactCoverageReceipt : Set

open ReceiptPackageCheck public

record ReceiptReproductionCheck
    (receipt : ExternalStudyReceipt)
    (package : ReceiptPackageCheck receipt) : Set where
  constructor receiptReproductionCheck
  field
    producerReexecuted : Bool
    reportedIntermediateArraysRecomputed : Bool
    reportedScoresRecomputed : Bool
    reportedStatisticalTestsRecomputed : Bool
    heldOutEvaluationRecomputed : Bool
    reproductionComparisonReceipt : Set

open ReceiptReproductionCheck public

record ExternalReceiptAdmissionBoundary : Set where
  constructor externalReceiptAdmissionBoundary
  field
    hashValidPackageCountsAsIndependentReproduction : Bool
    hashValidPackageCountsAsIndependentReproductionIsFalse :
      hashValidPackageCountsAsIndependentReproduction ≡ false

    reproducedPublishedMetricCountsAsSemanticRealization : Bool
    reproducedPublishedMetricCountsAsSemanticRealizationIsFalse :
      reproducedPublishedMetricCountsAsSemanticRealization ≡ false

    reproducedFitCountsAsRobustModelAdequacy : Bool
    reproducedFitCountsAsRobustModelAdequacyIsFalse :
      reproducedFitCountsAsRobustModelAdequacy ≡ false

    checkedReceiptCanFeedStage67EvidenceLayer : Bool
    checkedReceiptCanFeedStage67EvidenceLayerIsTrue :
      checkedReceiptCanFeedStage67EvidenceLayer ≡ true

canonicalExternalReceiptAdmissionBoundary : ExternalReceiptAdmissionBoundary
canonicalExternalReceiptAdmissionBoundary =
  externalReceiptAdmissionBoundary
    false refl
    false refl
    false refl
    true refl

artifactInferenceDestination :
  Study.ValidationArtifact → TOE.InferenceStage
artifactInferenceDestination = TOE.artifactInferenceStage

record ExternalPayloadPresence : Set where
  constructor externalPayloadPresence
  field
    actualExternalPayloadAttached : Bool
    actualExternalPayloadAttachedIsFalse :
      actualExternalPayloadAttached ≡ false

currentExternalPayloadPresence : ExternalPayloadPresence
currentExternalPayloadPresence =
  externalPayloadPresence false refl
