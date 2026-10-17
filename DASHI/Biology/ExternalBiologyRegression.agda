module DASHI.Biology.ExternalBiologyRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.ExternalBiologyEvidenceCore as External
import DASHI.Biology.ExternalBiologyMappingRevisionExact as Mapping
import DASHI.Biology.ExternalBiologyConsumerAdmissionExact as Admission
import DASHI.Biology.UniProtExternalKnowledgeExact as UniProt
import DASHI.Biology.KitzerowUniProtCrossPollinationExact as Bridge

------------------------------------------------------------------------
-- Regression witnesses for the external-biology source boundary.
-- These intentionally fail to typecheck until the production owners exist.
------------------------------------------------------------------------

datasetAssertionDoesNotCreateTruth :
  External.ClaimBoundary.datasetAssertionCreatesBiologicalTruth
    External.canonicalClaimBoundary ≡ false
datasetAssertionDoesNotCreateTruth = refl

reviewedDoesNotMeanExperimentallyProved :
  External.ClaimBoundary.reviewedStatusImpliesDirectExperimentalProof
    External.canonicalClaimBoundary ≡ false
reviewedDoesNotMeanExperimentallyProved = refl

mappingDoesNotCollapseIdentity :
  Mapping.MappingBoundary.crossReferenceAloneCreatesEntityIdentity
    Mapping.canonicalMappingBoundary ≡ false
mappingDoesNotCollapseIdentity = refl

revisionAbsenceDoesNotMeanNonexistence :
  Mapping.RevisionBoundary.absenceFromCurrentDatasetMeansBiologicalNonexistence
    Mapping.canonicalRevisionBoundary ≡ false
revisionAbsenceDoesNotMeanNonexistence = refl

admissionDoesNotCreateTruth :
  Admission.AdmissionBoundary.consumerAdmissionCreatesBiologicalTruth
    Admission.canonicalAdmissionBoundary ≡ false
admissionDoesNotCreateTruth = refl

qdprIsReviewed :
  External.reviewStatus UniProt.qdprProtein ≡ External.reviewed
qdprIsReviewed = refl

qdprCanonicalSequenceVersionIsTwo :
  External.sequenceVersion UniProt.qdprProtein ≡ 2
qdprCanonicalSequenceVersionIsTwo = refl

qdprClaimDoesNotConfirmWholeKitzerowGraph :
  Bridge.KitzerowUniProtBoundary.qdprNodeSupportConfirmsWholeGraph
    Bridge.canonicalKitzerowUniProtBoundary ≡ false
qdprClaimDoesNotConfirmWholeKitzerowGraph = refl

uniprotDoesNotEstablishKitzerowPriority :
  Bridge.KitzerowUniProtBoundary.uniprotAnnotationEstablishesKitzerowPriority
    Bridge.canonicalKitzerowUniProtBoundary ≡ false
uniprotDoesNotEstablishKitzerowPriority = refl

uniprotDoesNotEstablishAttributionBreach :
  Bridge.KitzerowUniProtBoundary.uniprotAnnotationEstablishesAttributionBreach
    Bridge.canonicalKitzerowUniProtBoundary ≡ false
uniprotDoesNotEstablishAttributionBreach = refl
