module DASHI.Biology.ExternalBiologyConsumerAdmissionExact where

open import DASHI.Core.Prelude

import DASHI.Biology.ExternalBiologyEvidenceCore as External
import DASHI.Core.GenericReceipt as Receipt

------------------------------------------------------------------------
-- CONSUMER-SPECIFIC ADMISSIBILITY
------------------------------------------------------------------------

data BiologicalConsumer : Set where
  exploratoryHypothesisConsumer : BiologicalConsumer
  sequenceIdentityConsumer : BiologicalConsumer
  structuralGeometryConsumer : BiologicalConsumer
  reactionAnnotationConsumer : BiologicalConsumer
  mechanisticModelConsumer : BiologicalConsumer
  directExperimentalMechanismConsumer : BiologicalConsumer
  clinicalActionConsumer : BiologicalConsumer

data EvidenceGrade : Set where
  predictionGrade : EvidenceGrade
  databaseAnnotationGrade : EvidenceGrade
  curatedLiteratureGrade : EvidenceGrade
  directExperimentalGrade : EvidenceGrade
  unresolvedGrade : EvidenceGrade

data AdmissionStatus : Set where
  admissible : AdmissionStatus
  insufficient : AdmissionStatus
  unresolved : AdmissionStatus

record ConsumerAssessment : Set where
  constructor consumerAssessment
  field
    assessmentId : String
    claim : External.BiologicalClaim
    consumer : BiologicalConsumer
    grade : EvidenceGrade
    status : AdmissionStatus
    rationale : String
    missingPaymentReference : String
    admissionCreatesBiologicalTruth : Bool
    admissionCreatesBiologicalTruthIsFalse :
      admissionCreatesBiologicalTruth ≡ false

open ConsumerAssessment public

mkAssessment :
  String → External.BiologicalClaim → BiologicalConsumer → EvidenceGrade →
  AdmissionStatus → String → String → ConsumerAssessment
mkAssessment assessmentId claim consumer grade status rationale missing =
  consumerAssessment assessmentId claim consumer grade status rationale missing false refl

record AdmissionBoundary : Set where
  constructor admissionBoundary
  field
    consumerAdmissionCreatesBiologicalTruth : Bool
    consumerAdmissionCreatesBiologicalTruthIsFalse :
      consumerAdmissionCreatesBiologicalTruth ≡ false
    exploratoryAdmissionImpliesMechanisticProof : Bool
    exploratoryAdmissionImpliesMechanisticProofIsFalse :
      exploratoryAdmissionImpliesMechanisticProof ≡ false
    structurePredictionSufficesForExperimentalStructureConsumer : Bool
    structurePredictionSufficesForExperimentalStructureConsumerIsFalse :
      structurePredictionSufficesForExperimentalStructureConsumer ≡ false
    curatedDatabaseAnnotationSufficesForClinicalAction : Bool
    curatedDatabaseAnnotationSufficesForClinicalActionIsFalse :
      curatedDatabaseAnnotationSufficesForClinicalAction ≡ false

canonicalAdmissionBoundary : AdmissionBoundary
canonicalAdmissionBoundary =
  admissionBoundary false refl false refl false refl false refl

canonicalExternalBiologyConsumerAdmissionReceipt : Receipt.GenericReceipt
canonicalExternalBiologyConsumerAdmissionReceipt =
  Receipt.mkNonPromotingReceipt
    "external biology consumer admission"
    "DASHI.Biology.ExternalBiologyConsumerAdmissionExact"
    "BiologicalConsumer / EvidenceGrade / ConsumerAssessment"
    "makes evidence sufficiency consumer-relative so exploratory, sequence, structural, mechanistic, experimental and clinical consumers cannot silently share one threshold"
    "admission is not truth; prediction is not experiment; database curation alone does not authorize clinical action"
    "agda -i . DASHI/Biology/ExternalBiologyConsumerAdmissionExact.agda"
