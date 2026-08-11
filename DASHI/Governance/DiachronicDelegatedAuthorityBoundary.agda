module DASHI.Governance.DiachronicDelegatedAuthorityBoundary where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Governance.GuardedPropositionResponseTree as Guarded
import DASHI.Algebra.Trit as Trit

data TemporalRole : Set where
  decisionSubjectRole caregiverSupporterRole delegatedAttorneyRole : TemporalRole
  serviceInstitutionRole neutralAdjudicatorRole neutralArchiveCustodianRole : TemporalRole

record WillSnapshot : Set where
  constructor willSnapshot
  field
    snapshotTime : Nat
    snapshotNode : Guarded.PropositionNode
    snapshotResponse : Guarded.ResponseState
    snapshotProvenance : String

open WillSnapshot public

data MandateSource : Set where
  formalAuthoritySource contemporaneousInstructionSource recordedPriorInstructionSource : MandateSource
  establishedPracticeSource urgentPerceivedRiskSource : MandateSource

record DelegatedMandate : Set where
  constructor delegatedMandate
  field
    subjectRole supporterRole : TemporalRole
    mandateSources : List MandateSource
    active revocable : Bool
    mandateScope : List Guarded.PropositionNode
    mandateProvenance : String

open DelegatedMandate public

record RevocationEvent : Set where
  constructor revocationEvent
  field
    revocationTime : Nat
    revokedMandate : DelegatedMandate
    prospectiveTermination historicalErasure : Bool
    currentInstruction : WillSnapshot

open RevocationEvent public

canonicalRevocationEvent : RevocationEvent
canonicalRevocationEvent =
  revocationEvent 10
    (delegatedMandate decisionSubjectRole caregiverSupporterRole
      (formalAuthoritySource ∷ recordedPriorInstructionSource ∷ establishedPracticeSource ∷ [])
      false true [] "abstract pre-existing delegated role")
    true false
    (willSnapshot 10 Guarded.canonicalCommitNode
      (Guarded.responseState Trit.neg Guarded.absentZero true true true "present refusal")
      "current decision-specific refusal")

canonicalRevocationPreservesHistory : historicalErasure canonicalRevocationEvent ≡ false
canonicalRevocationPreservesHistory = refl

data AutonomyModel : Set where synchronicAutonomy diachronicAutonomy supportedIntegratedAutonomy : AutonomyModel

data TemporalConsistencyStatus : Set where
  temporallyConsistent authenticChangeCandidate stateDependentChangeCandidate : TemporalConsistencyStatus
  undueInfluenceCandidate unresolvedTemporalConflict : TemporalConsistencyStatus

record TemporalWillConflict : Set where
  constructor temporalWillConflict
  field
    priorSnapshots : List WillSnapshot
    presentSnapshot : WillSnapshot
    selectedAutonomyModel : AutonomyModel
    consistencyStatus : TemporalConsistencyStatus
    neutralDiscriminatorAvailable : Bool
    conflictReading : String

record SupportedDecisionConditions : Set where
  constructor supportedDecisionConditions
  field
    presentVoicePreserved accessibleInformation communicationSupport : Bool
    traumaSensitiveContext freedomFromUndueInfluence opportunityForRevision : Bool
    supporterCannotSelfAuthoriseOverride : Bool

open SupportedDecisionConditions public

record MeaningfullySupportedDecision (conditions : SupportedDecisionConditions) : Set where
  constructor meaningfullySupportedDecision
  field
    presentVoiceWitness : presentVoicePreserved conditions ≡ true
    informationWitness : accessibleInformation conditions ≡ true
    communicationWitness : communicationSupport conditions ≡ true
    traumaContextWitness : traumaSensitiveContext conditions ≡ true
    undueInfluenceWitness : freedomFromUndueInfluence conditions ≡ true
    revisionWitness : opportunityForRevision conditions ≡ true
    noSelfAuthorisedOverrideWitness : supporterCannotSelfAuthoriseOverride conditions ≡ true

canonicalSupportedDecisionConditions : SupportedDecisionConditions
canonicalSupportedDecisionConditions = supportedDecisionConditions true true true true true true true

canonicalMeaningfullySupportedDecision : MeaningfullySupportedDecision canonicalSupportedDecisionConditions
canonicalMeaningfullySupportedDecision = meaningfullySupportedDecision refl refl refl refl refl refl refl

data ArchiveUse : Set where
  memoryAidUse disabilityAccommodationUse instructionRepositoryUse legalEvidenceUse : ArchiveUse
  sharedCareInfrastructureUse privateDataUse revocableAccessDomainUse : ArchiveUse

data AccessStatus : Set where authorisedAccess contestedAccess revokedAccess : AccessStatus

data ArchiveOperation : Set where
  preserveExistingData retrieveKnownRelevantRecord broadExploratorySearch : ArchiveOperation
  monitorNewActivity alterCredentialsOrFiles : ArchiveOperation

record ArchiveBoundary : Set where
  constructor archiveBoundary
  field
    archiveUses : List ArchiveUse
    accessStatus : AccessStatus
    neutralCustodianAvailable : Bool
    allowedOperations : List ArchiveOperation
    archiveReading : String

canonicalContestedArchiveBoundary : ArchiveBoundary
canonicalContestedArchiveBoundary =
  archiveBoundary
    (memoryAidUse ∷ disabilityAccommodationUse ∷ instructionRepositoryUse ∷ legalEvidenceUse ∷ sharedCareInfrastructureUse ∷ privateDataUse ∷ revocableAccessDomainUse ∷ [])
    contestedAccess true
    (preserveExistingData ∷ retrieveKnownRelevantRecord ∷ [])
    "Historical evidentiary relevance and current privacy coexist; neutral custody separates preservation/retrieval from monitoring or control."

data EvidentiaryProposition : Set where
  previouslyAuthorisedProposition previouslyExpressedValueProposition : EvidentiaryProposition
  goodFaithContinuingMandateBeliefProposition authorityActuallyContinuedProposition : EvidentiaryProposition

data EvidenceStrength : Set where noEvidence relevantEvidence strongEvidence conclusiveEvidence : EvidenceStrength

record RecordedWillEvidence : Set where
  constructor recordedWillEvidence
  field
    recordedSnapshots : List WillSnapshot
    previouslyAuthorisedStrength previouslyExpressedValueStrength : EvidenceStrength
    goodFaithBeliefStrength actualContinuingAuthorityStrength : EvidenceStrength

open RecordedWillEvidence public

canonicalRecordedWillEvidence : RecordedWillEvidence
canonicalRecordedWillEvidence = recordedWillEvidence [] strongEvidence strongEvidence strongEvidence relevantEvidence

canonicalActualAuthorityNotConclusive : actualContinuingAuthorityStrength canonicalRecordedWillEvidence ≡ relevantEvidence
canonicalActualAuthorityNotConclusive = refl

data ProcessStepKind : Set where
  alreadyCompletedStep unavoidableContinuationStep requiredClosureStep newDiscretionaryStep : ProcessStepKind

freshAuthorisationRequired : ProcessStepKind → Bool
freshAuthorisationRequired alreadyCompletedStep = false
freshAuthorisationRequired unavoidableContinuationStep = false
freshAuthorisationRequired requiredClosureStep = false
freshAuthorisationRequired newDiscretionaryStep = true

newDiscretionaryStepRequiresFreshAuthorisation : freshAuthorisationRequired newDiscretionaryStep ≡ true
newDiscretionaryStepRequiresFreshAuthorisation = refl

unavoidableContinuationDoesNotRequireFreshStartAuthority :
  freshAuthorisationRequired unavoidableContinuationStep ≡ false
unavoidableContinuationDoesNotRequireFreshStartAuthority = refl

data InertiaKind : Set where institutionalInertia technicalInertia legalInertia practicalInertia : InertiaKind

record ProcessInertia : Set where
  constructor processInertia
  field
    processLabel : String
    authorisedStart : Bool
    revocationTime : Nat
    inertiaKinds : List InertiaKind
    postRevocationSteps : List ProcessStepKind
    stoppabilityReading : String

record NecessityAssessment : Set where
  constructor necessityAssessment
  field
    seriousRiskPerceived lessRestrictiveAlternativeKnown actionTimeLimited : Bool
    periodicallyReviewed intrusionAcknowledged : Bool
    exAnteEvidence realisedOutcome : String

record DiachronicAuthorityPromotionBoundary : Set where
  constructor diachronicAuthorityPromotionBoundary
  field
    priorMandateMeansUnlimitedAuthority : Bool
    priorMandateMeansUnlimitedAuthorityIsFalse : priorMandateMeansUnlimitedAuthority ≡ false
    revocationErasesHistory : Bool
    revocationErasesHistoryIsFalse : revocationErasesHistory ≡ false
    historicalEvidenceRestoresAuthority : Bool
    historicalEvidenceRestoresAuthorityIsFalse : historicalEvidenceRestoresAuthority ≡ false
    noCurrentAuthorityMeansNoEvidence : Bool
    noCurrentAuthorityMeansNoEvidenceIsFalse : noCurrentAuthorityMeansNoEvidence ≡ false
    evidentiaryRelevanceMeansAuthority : Bool
    evidentiaryRelevanceMeansAuthorityIsFalse : evidentiaryRelevanceMeansAuthority ≡ false
    presentWillInfallibleAboutItsReliability : Bool
    presentWillInfallibleAboutItsReliabilityIsFalse : presentWillInfallibleAboutItsReliability ≡ false
    allegedImpairmentNullifiesPresentWill : Bool
    allegedImpairmentNullifiesPresentWillIsFalse : allegedImpairmentNullifiesPresentWill ≡ false
    goodOutcomeProvesGoodExAnteProbability : Bool
    goodOutcomeProvesGoodExAnteProbabilityIsFalse : goodOutcomeProvesGoodExAnteProbability ≡ false
    authorityBoundaryReading : String

open DiachronicAuthorityPromotionBoundary public

canonicalDiachronicAuthorityPromotionBoundary : DiachronicAuthorityPromotionBoundary
canonicalDiachronicAuthorityPromotionBoundary =
  diachronicAuthorityPromotionBoundary
    false refl false refl false refl false refl false refl false refl false refl false refl
    "Revocation terminates prospective delegated authority without erasing prior instructions. Historical evidence remains relevant without restoring authority. Present will is presumptively important but not self-validating evidence of its own reliability, and alleged impairment does not automatically nullify it."

canonicalHistoricalEvidenceRestoresAuthorityFalse :
  historicalEvidenceRestoresAuthority canonicalDiachronicAuthorityPromotionBoundary ≡ false
canonicalHistoricalEvidenceRestoresAuthorityFalse =
  historicalEvidenceRestoresAuthorityIsFalse canonicalDiachronicAuthorityPromotionBoundary
