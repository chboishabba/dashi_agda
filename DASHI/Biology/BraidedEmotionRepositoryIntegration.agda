module DASHI.Biology.BraidedEmotionRepositoryIntegration where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)

import DASHI.Biology.BraidedEmotionProcessBoundary as Emotion
import DASHI.Biology.BraidedEmotionTheoryContention as Contention
import DASHI.Biology.BraidedEmotionObservationBridge as Observation
import DASHI.Biology.RelationalQiBodyMemoryBridge as Qi
import DASHI.Biology.FormalLayerExplanationBoundary as Explanation
import DASHI.Biology.TraumaClinicalGovernanceBoundary as Governance
import DASHI.Biology.TraumaBodyMemoryCandidateBridge as BodyMemory

------------------------------------------------------------------------
-- Repository-native integration facade.
--
-- This module prevents the braided emotion ontology from becoming a parallel
-- island.  It carries canonical repository records directly and exposes the
-- equalities and authority gates required for downstream consumers.

data IntegrationAxis : Set where
  emotionProcessAxis : IntegrationAxis
  theoryContentionAxis : IntegrationAxis
  observationSeparationAxis : IntegrationAxis
  relationalQiAxis : IntegrationAxis
  explanationBoundaryAxis : IntegrationAxis
  clinicalGovernanceAxis : IntegrationAxis
  bodyMemoryFacadeAxis : IntegrationAxis
  antiExtractionAxis : IntegrationAxis
  candidateOnlyAxis : IntegrationAxis

canonicalIntegrationAxes : List IntegrationAxis
canonicalIntegrationAxes =
  emotionProcessAxis
  ∷ theoryContentionAxis
  ∷ observationSeparationAxis
  ∷ relationalQiAxis
  ∷ explanationBoundaryAxis
  ∷ clinicalGovernanceAxis
  ∷ bodyMemoryFacadeAxis
  ∷ antiExtractionAxis
  ∷ candidateOnlyAxis
  ∷ []

canonicalIntegrationNotes : List String
canonicalIntegrationNotes =
  "The emotion process boundary remains candidate-only and non-reductive"
  ∷ "Theory disagreement is represented by typed scale and contention rows"
  ∷ "Episode label report bodily proxy neural proxy and relation remain distinct"
  ∷ "Relational Qi PatternMind reciprocity kin story place breath and long-time are imported from the canonical repository bridge"
  ∷ "Cultural narrative remains guide/context and does not become typed proof or authority"
  ∷ "Diagnosis treatment prescription exposure forcing and vulnerable-user authority remain blocked by canonical governance"
  ∷ "The trauma/body-memory facade remains an imported candidate integration surface rather than an emotion diagnosis"
  ∷ "Cultural extraction empirical capture universalisation and substitution for living practice remain blocked"
  ∷ []

record BraidedEmotionRepositoryIntegration : Setω where
  field
    emotionBoundary : Emotion.BraidedEmotionBoundary
    emotionBoundaryIsCanonical :
      emotionBoundary ≡ Emotion.canonicalBraidedEmotionBoundary

    contentionReceipt : Contention.PreservedContentionReceipt
    contentionReceiptIsCanonical :
      contentionReceipt ≡ Contention.canonicalPreservedContentionReceipt

    observationReceipt : Observation.ObservationSeparationReceipt
    observationReceiptIsCanonical :
      observationReceipt ≡ Observation.canonicalObservationSeparationReceipt

    relationalQiRegistry : Qi.RelationalQiBridgeRegistry
    relationalQiRegistryIsCanonical :
      relationalQiRegistry ≡ Qi.canonicalRelationalQiBridgeRegistry

    explanationBoundary : Explanation.ReaderComprehensionBoundary
    explanationBoundaryIsCanonical :
      explanationBoundary ≡ Explanation.canonicalReaderComprehensionBoundary

    traumaGovernance : Governance.TraumaClinicalGovernanceBoundary
    traumaGovernanceIsCanonical :
      traumaGovernance ≡ Governance.canonicalTraumaClinicalGovernanceBoundary

    bodyMemoryFacade : BodyMemory.TraumaBodyMemoryCandidateBridge
    bodyMemoryFacadeIsCanonical :
      bodyMemoryFacade ≡ BodyMemory.canonicalTraumaBodyMemoryCandidateBridge

    diagnosisAuthorityBlocked :
      Governance.diagnosisAuthority traumaGovernance ≡ false

    treatmentPrescriptionAuthorityBlocked :
      Governance.treatmentPrescriptionAuthority traumaGovernance ≡ false

    exposureForcingAuthorityBlocked :
      Governance.exposureForcingAuthority traumaGovernance ≡ false

    vulnerableUserAuthorityBlocked :
      Governance.vulnerableUserAuthority traumaGovernance ≡ false

    consentGateRequired :
      Governance.consentGateRequired traumaGovernance ≡ true

    pacingGateRequired :
      Governance.pacingGateRequired traumaGovernance ≡ true

    reviewGateRequired :
      Governance.reviewGateRequired traumaGovernance ≡ true

    culturalExtractionAuthorityBlocked :
      Qi.registryCulturalExtractionAuthority relationalQiRegistry ≡ false

    empiricalValidationAuthorityBlocked :
      Qi.registryEmpiricalValidationAuthority relationalQiRegistry ≡ false

    clinicalTreatmentAuthorityBlocked :
      Qi.registryClinicalTreatmentAuthority relationalQiRegistry ≡ false

    diagnosisAuthorityAlsoBlockedByQiBoundary :
      Qi.registryDiagnosisAuthority relationalQiRegistry ≡ false

    provenanceAndLivingPracticeBoundaryPreserved : Bool
    provenanceAndLivingPracticeBoundaryPreservedIsTrue :
      provenanceAndLivingPracticeBoundaryPreserved ≡ true

    narrativeDoesNotBecomeProofOrAuthority : Bool
    narrativeDoesNotBecomeProofOrAuthorityIsTrue :
      narrativeDoesNotBecomeProofOrAuthority ≡ true

    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true

    integrationAxes : List IntegrationAxis
    integrationAxesAreCanonical : integrationAxes ≡ canonicalIntegrationAxes

    integrationNotes : List String
    integrationNotesAreCanonical : integrationNotes ≡ canonicalIntegrationNotes

open BraidedEmotionRepositoryIntegration public

canonicalBraidedEmotionRepositoryIntegration :
  BraidedEmotionRepositoryIntegration
canonicalBraidedEmotionRepositoryIntegration =
  record
    { emotionBoundary = Emotion.canonicalBraidedEmotionBoundary
    ; emotionBoundaryIsCanonical = refl
    ; contentionReceipt = Contention.canonicalPreservedContentionReceipt
    ; contentionReceiptIsCanonical = refl
    ; observationReceipt = Observation.canonicalObservationSeparationReceipt
    ; observationReceiptIsCanonical = refl
    ; relationalQiRegistry = Qi.canonicalRelationalQiBridgeRegistry
    ; relationalQiRegistryIsCanonical = refl
    ; explanationBoundary = Explanation.canonicalReaderComprehensionBoundary
    ; explanationBoundaryIsCanonical = refl
    ; traumaGovernance = Governance.canonicalTraumaClinicalGovernanceBoundary
    ; traumaGovernanceIsCanonical = refl
    ; bodyMemoryFacade = BodyMemory.canonicalTraumaBodyMemoryCandidateBridge
    ; bodyMemoryFacadeIsCanonical = refl
    ; diagnosisAuthorityBlocked =
        Governance.diagnosisAuthorityIsFalse
          Governance.canonicalTraumaClinicalGovernanceBoundary
    ; treatmentPrescriptionAuthorityBlocked =
        Governance.treatmentPrescriptionAuthorityIsFalse
          Governance.canonicalTraumaClinicalGovernanceBoundary
    ; exposureForcingAuthorityBlocked =
        Governance.exposureForcingAuthorityIsFalse
          Governance.canonicalTraumaClinicalGovernanceBoundary
    ; vulnerableUserAuthorityBlocked =
        Governance.vulnerableUserAuthorityIsFalse
          Governance.canonicalTraumaClinicalGovernanceBoundary
    ; consentGateRequired =
        Governance.consentGateRequiredIsTrue
          Governance.canonicalTraumaClinicalGovernanceBoundary
    ; pacingGateRequired =
        Governance.pacingGateRequiredIsTrue
          Governance.canonicalTraumaClinicalGovernanceBoundary
    ; reviewGateRequired =
        Governance.reviewGateRequiredIsTrue
          Governance.canonicalTraumaClinicalGovernanceBoundary
    ; culturalExtractionAuthorityBlocked =
        Qi.registryCulturalExtractionAuthorityIsFalse
          Qi.canonicalRelationalQiBridgeRegistry
    ; empiricalValidationAuthorityBlocked =
        Qi.registryEmpiricalValidationAuthorityIsFalse
          Qi.canonicalRelationalQiBridgeRegistry
    ; clinicalTreatmentAuthorityBlocked =
        Qi.registryClinicalTreatmentAuthorityIsFalse
          Qi.canonicalRelationalQiBridgeRegistry
    ; diagnosisAuthorityAlsoBlockedByQiBoundary =
        Qi.registryDiagnosisAuthorityIsFalse
          Qi.canonicalRelationalQiBridgeRegistry
    ; provenanceAndLivingPracticeBoundaryPreserved = true
    ; provenanceAndLivingPracticeBoundaryPreservedIsTrue = refl
    ; narrativeDoesNotBecomeProofOrAuthority = true
    ; narrativeDoesNotBecomeProofOrAuthorityIsTrue = refl
    ; candidateOnly = true
    ; candidateOnlyIsTrue = refl
    ; integrationAxes = canonicalIntegrationAxes
    ; integrationAxesAreCanonical = refl
    ; integrationNotes = canonicalIntegrationNotes
    ; integrationNotesAreCanonical = refl
    }
