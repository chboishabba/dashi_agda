module DASHI.Law.IndependentEvidenceProvenanceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Law.CoerciveEncounterLawfulnessBidiExact as Law

------------------------------------------------------------------------
-- Evidence provenance is not reducible to evidence presence.
------------------------------------------------------------------------

data ProducerRelation : Set where
  actorUnderReview sameInstitution independentInstitution independentThirdParty : ProducerRelation

data CorroborationState : Set where
  uncorroborated internallyCorroborated independentlyCorroborated : CorroborationState

data AcquisitionMode : Set where
  officerReport bodyCamera deviceTelemetry medicalRecord civilianVideo witnessStatement : AcquisitionMode

record EvidenceReceipt : Set where
  constructor evidenceReceipt
  field
    evidenceState : Law.EvidenceState
    producerRelation : ProducerRelation
    acquisitionMode : AcquisitionMode
    corroboration : CorroborationState
    immutableOrTamperEvident : Bool
    contemporaneous : Bool
    receiptReference : String

open EvidenceReceipt public

independentReceipt : EvidenceReceipt → Set
independentReceipt r = producerRelation r ≡ independentInstitution ⊎ producerRelation r ≡ independentThirdParty

record IndependentPromotionReceipt (r : EvidenceReceipt) : Set where
  constructor independentPromotionReceipt
  field
    positive : evidenceState r ≡ Law.positiveReceipt
    independent : independentReceipt r
    promotedCorroboration : corroboration r ≡ independentlyCorroborated

open IndependentPromotionReceipt public

------------------------------------------------------------------------
-- Same observed content may have different provenance strength.
------------------------------------------------------------------------

data EvidenceContent : Set where
  noForceRecorded : EvidenceContent

data ProvenanceStrength : Set where
  dependentStrength independentStrength : ProvenanceStrength

data ProvenanceWitnessState : Set where
  sameContentDependent sameContentIndependent : ProvenanceWitnessState

contentProjection : ProvenanceWitnessState → EvidenceContent
contentProjection sameContentDependent = noForceRecorded
contentProjection sameContentIndependent = noForceRecorded

provenanceStrength : ProvenanceWitnessState → ProvenanceStrength
provenanceStrength sameContentDependent = dependentStrength
provenanceStrength sameContentIndependent = independentStrength

provenanceStrengthDiffers :
  provenanceStrength sameContentDependent ≡ provenanceStrength sameContentIndependent → ⊥
provenanceStrengthDiffers ()

contentDoesNotDetermineIndependence :
  NF.NonFactorabilityWitness contentProjection provenanceStrength
contentDoesNotDetermineIndependence =
  NF.nonFactorabilityWitness
    sameContentDependent sameContentIndependent refl provenanceStrengthDiffers

sameContentCannotReconstructIndependence :
  NF.FactorsThrough contentProjection provenanceStrength → ⊥
sameContentCannotReconstructIndependence =
  NF.witnessRulesOutEveryFlatFactorisation contentDoesNotDetermineIndependence

------------------------------------------------------------------------
-- Accountability reconstruction deficit.
------------------------------------------------------------------------

record AuditSurface : Set where
  constructor auditSurface
  field
    physicalTrace : Bool
    bodyCamera : Bool
    telemetry : Bool
    medicalEvidence : Bool
    independentWitness : Bool
    producerIndependent : Bool
    auditReference : String

open AuditSurface public

record AccountabilityReconstructionDeficit (surface : AuditSurface) : Set where
  constructor accountabilityReconstructionDeficit
  field
    noPhysicalTrace : physicalTrace surface ≡ false
    noBodyCamera : bodyCamera surface ≡ false
    noTelemetry : telemetry surface ≡ false
    noMedicalEvidence : medicalEvidence surface ≡ false
    noIndependentWitness : independentWitness surface ≡ false
    noIndependentProducer : producerIndependent surface ≡ false

open AccountabilityReconstructionDeficit public

canonicalLowAuditSurface : AuditSurface
canonicalLowAuditSurface =
  auditSurface false false false false false false
    "abstract low-observability, producer-dependent audit surface"

canonicalAccountabilityDeficit :
  AccountabilityReconstructionDeficit canonicalLowAuditSurface
canonicalAccountabilityDeficit =
  accountabilityReconstructionDeficit refl refl refl refl refl refl

------------------------------------------------------------------------
-- Boundaries.
------------------------------------------------------------------------

record EvidenceProvenanceBoundary : Set where
  constructor evidenceProvenanceBoundary
  field
    recordedByActorUnderReviewMeansIndependent : Bool
    recordedByActorUnderReviewMeansIndependentIsFalse :
      recordedByActorUnderReviewMeansIndependent ≡ false
    sameInstitutionMeansIndependentByDefault : Bool
    sameInstitutionMeansIndependentByDefaultIsFalse :
      sameInstitutionMeansIndependentByDefault ≡ false
    evidencePresenceDeterminesProvenanceStrength : Bool
    evidencePresenceDeterminesProvenanceStrengthIsFalse :
      evidencePresenceDeterminesProvenanceStrength ≡ false
    missingIndependentChannelProvesMisconduct : Bool
    missingIndependentChannelProvesMisconductIsFalse :
      missingIndependentChannelProvesMisconduct ≡ false

canonicalEvidenceProvenanceBoundary : EvidenceProvenanceBoundary
canonicalEvidenceProvenanceBoundary =
  evidenceProvenanceBoundary false refl false refl false refl false refl
