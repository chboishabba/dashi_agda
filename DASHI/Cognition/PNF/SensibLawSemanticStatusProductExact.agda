module DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawSpacyCompositionOnlySemanticConstitutionExact as Constitution
import DASHI.Cognition.PNF.SensibLawLegalSemanticAdmissionFrontierExact as Admission

------------------------------------------------------------------------
-- ORTHOGONAL SEMANTIC STATUS PRODUCT
--
-- These coordinates are intentionally independent.  Parser observation,
-- syntactic role, semantic role, referent identity, antecedent/coreference,
-- event occurrence, proposition status, evidence, modality, time and legal
-- applicability must not collapse into one undifferentiated "semantic fact".
------------------------------------------------------------------------

data ParticipantRole : Set where
  agent patient theme experiencer recipient beneficiary instrument
  location source goal cause participantUnresolved : ParticipantRole

data LegalParticipantRole : Set where
  claimant respondent applicant authority decisionMaker
  rightsBearer dutyBearer powerHolder liabilityBearer
  legalParticipantUnresolved : LegalParticipantRole

data ReferentKind : Set where
  entityReferent eventualityReferent propositionReferent timeReferent
  placeReferent ruleReferent documentReferent spanReferent unknownReferent
  : ReferentKind

data IdentityStatus : Set where
  identityUnresolved : IdentityStatus
  identityCandidateSet : IdentityStatus
  identityResolvedSame : IdentityStatus
  identityResolvedDistinct : IdentityStatus
  identityNotMaterialToConsumer : IdentityStatus

data AntecedentStatus : Set where
  antecedentUnresolved : AntecedentStatus
  antecedentCandidateSet : AntecedentStatus
  antecedentNarrowed : AntecedentStatus
  antecedentResolved : AntecedentStatus
  antecedentNotMaterialToConsumer : AntecedentStatus

data OccurrenceStatus : Set where
  occurrenceUnresolved : OccurrenceStatus
  mentionedEventuality : OccurrenceStatus
  assertedOccurrence : OccurrenceStatus
  reportedOccurrence : OccurrenceStatus
  allegedOccurrence : OccurrenceStatus
  hypotheticalOccurrence : OccurrenceStatus
  conditionalOccurrence : OccurrenceStatus
  negatedOccurrence : OccurrenceStatus
  counterfactualOccurrence : OccurrenceStatus
  plannedFutureOccurrence : OccurrenceStatus
  questionedOccurrence : OccurrenceStatus
  occurrenceAdmitted : OccurrenceStatus

data PropositionStatus : Set where
  propositionUnresolved : PropositionStatus
  propositionRepresented : PropositionStatus
  assertedBySource : PropositionStatus
  allegedProposition : PropositionStatus
  admittedProposition : PropositionStatus
  deniedProposition : PropositionStatus
  foundAsFact : PropositionStatus
  heldByCourt : PropositionStatus
  assumedProposition : PropositionStatus
  hypotheticalProposition : PropositionStatus
  quotedReportedProposition : PropositionStatus
  distinguishedProposition : PropositionStatus
  rejectedProposition : PropositionStatus
  notDeterminedProposition : PropositionStatus

data TruthStatus : Set where
  truthUnresolved : TruthStatus
  candidateTrue : TruthStatus
  candidateFalse : TruthStatus
  truthAdmitted : TruthStatus
  falsityAdmitted : TruthStatus

data AttributionRole : Set where
  author speaker reporter quotedSpeaker propositionSource
  attributionUnresolved : AttributionRole

data EvidencePolarity : Set where
  evidenceFor evidenceAgainst evidenceNeutral evidencePolarityUnresolved
  : EvidencePolarity

data EvidenceKind : Set where
  sourceEvidence testimonialEvidence documentaryEvidence parserEvidence
  provenanceEvidence externalEvidence evidenceKindUnresolved : EvidenceKind

data ModalityKind : Set where
  deontic epistemic dynamicAbility bouletic teleological modalityKindUnresolved
  : ModalityKind

data ModalForce : Set where
  obligation permission prohibition possibility necessity modalForceUnresolved
  : ModalForce

data ScopeStatus : Set where
  scopeUnresolved scopeLocalCandidate scopeResolved : ScopeStatus

data TemporalRelationKind : Set where
  eventTime referenceTime documentTime legalEffectiveTime
  validityInterval commencement expiry repeal amendment temporalRelationUnresolved
  : TemporalRelationKind

data ConditionKind : Set where
  antecedentCondition exceptionCondition defeaterCondition unlessCondition
  providedThatCondition subjectToCondition overrideCondition conditionUnresolved
  : ConditionKind

data JurisdictionKind : Set where
  geographicJurisdiction legalSystemJurisdiction courtJurisdiction
  personalJurisdiction subjectMatterJurisdiction jurisdictionUnresolved
  : JurisdictionKind

data AuthorityKind : Set where
  sourceAuthority legalAuthority institutionalAuthority promotionAuthority
  authorityUnresolved : AuthorityKind

data ApplicabilityStatus : Set where
  applicabilityUnresolved applicabilityCandidate applicabilityAdmitted
  inapplicabilityAdmitted : ApplicabilityStatus

data ViolationStatus : Set where
  violationUnresolved violationCandidate violationAdmitted noViolationAdmitted
  : ViolationStatus

data LiabilityStatus : Set where
  liabilityUnresolved liabilityCandidate liabilityAdmitted noLiabilityAdmitted
  : LiabilityStatus

data BurdenKind : Set where
  evidentialBurden persuasiveBurden burdenKindUnresolved : BurdenKind

data StandardOfProof : Set where
  beyondReasonableDoubt balanceOfProbabilities clearAndConvincing
  standardUnresolved : StandardOfProof

data JudicialDiscourseStatus : Set where
  holding ratioCandidate obiter findingOfFact submission allegation order
  disposition distinguished followed overruled judicialStatusUnresolved
  : JudicialDiscourseStatus

data NormativeRelation : Set where
  duty permissionRelation power liabilityRelation right privilege immunity
  disability normativeRelationUnresolved : NormativeRelation

------------------------------------------------------------------------
-- Status-bearing objects.  Identity and antecedent keep candidate fibres as
-- opaque references rather than selecting a member by construction.
------------------------------------------------------------------------

record SemanticSubject : Set where
  constructor semanticSubject
  field
    subjectReference : String
    referentKind : ReferentKind
    participantRole : ParticipantRole
    legalRole : LegalParticipantRole
    identityStatus : IdentityStatus
    antecedentStatus : AntecedentStatus

open SemanticSubject public

record EventStatusProduct : Set where
  constructor eventStatusProduct
  field
    eventReference : String
    occurrence : OccurrenceStatus
    eventTimeStatus : TemporalRelationKind
    eventPolarityScope : ScopeStatus

open EventStatusProduct public

record PropositionStatusProduct : Set where
  constructor propositionStatusProduct
  field
    propositionReference : String
    propositionStatus : PropositionStatus
    truthStatus : TruthStatus
    attribution : AttributionRole
    evidencePolarity : EvidencePolarity
    evidenceKind : EvidenceKind
    modalityKind : ModalityKind
    modalForce : ModalForce
    modalScope : ScopeStatus

open PropositionStatusProduct public

record LegalStatusProduct : Set where
  constructor legalStatusProduct
  field
    jurisdictionKind : JurisdictionKind
    authorityKind : AuthorityKind
    conditionKind : ConditionKind
    applicability : ApplicabilityStatus
    violation : ViolationStatus
    liability : LiabilityStatus
    burdenKind : BurdenKind
    standardOfProof : StandardOfProof
    judicialStatus : JudicialDiscourseStatus
    normativeRelation : NormativeRelation

open LegalStatusProduct public

record SemanticCommitmentState : Set where
  constructor semanticCommitmentState
  field
    sourceCandidate : Constitution.SemanticCandidateFibre
    subjects : List SemanticSubject
    events : List EventStatusProduct
    propositions : List PropositionStatusProduct
    legalStatuses : List LegalStatusProduct
    candidateOnly : Bool
    governedAdmissionPresent : Bool

open SemanticCommitmentState public

------------------------------------------------------------------------
-- Commitment ladder.  Advancement is receipt-shaped and monotone in authority:
-- a later stage may consume earlier evidence, but no early stage is definitionally
-- identified with a later one.
------------------------------------------------------------------------

data CommitmentStage : Set where
  observationStage syntacticStage semanticCandidateStage referenceCandidateStage
  contextResolvedStage statusQualifiedStage evidentialCommitmentStage
  governedAdmissionStage consumerConclusionStage : CommitmentStage

infix 4 _⇒stage_
data _⇒stage_ : CommitmentStage → CommitmentStage → Set where
  observationToSyntax : observationStage ⇒stage syntacticStage
  syntaxToSemanticCandidate : syntacticStage ⇒stage semanticCandidateStage
  semanticToReferenceCandidate : semanticCandidateStage ⇒stage referenceCandidateStage
  referenceToContext : referenceCandidateStage ⇒stage contextResolvedStage
  contextToStatus : contextResolvedStage ⇒stage statusQualifiedStage
  statusToEvidence : statusQualifiedStage ⇒stage evidentialCommitmentStage
  evidenceToAdmission : evidentialCommitmentStage ⇒stage governedAdmissionStage
  admissionToConsumer : governedAdmissionStage ⇒stage consumerConclusionStage

------------------------------------------------------------------------
-- Explicit resolution receipts.  These are deliberately distinct currencies.
------------------------------------------------------------------------

record IdentityResolutionReceipt : Set where
  constructor identityResolutionReceipt
  field
    subject : SemanticSubject
    resultingIdentityStatus : IdentityStatus
    candidateSetReference : String
    evidenceReferences : List String
    resolverReference : String
    policyReference : String

record AntecedentResolutionReceipt : Set where
  constructor antecedentResolutionReceipt
  field
    subject : SemanticSubject
    resultingAntecedentStatus : AntecedentStatus
    accessibilityWitnessReferences : List String
    candidateSetReference : String
    resolverReference : String

record OccurrenceResolutionReceipt : Set where
  constructor occurrenceResolutionReceipt
  field
    event : EventStatusProduct
    resultingOccurrenceStatus : OccurrenceStatus
    propositionSupportReferences : List String
    evidenceReferences : List String
    resolverReference : String

record PropositionResolutionReceipt : Set where
  constructor propositionResolutionReceipt
  field
    proposition : PropositionStatusProduct
    resultingPropositionStatus : PropositionStatus
    resultingTruthStatus : TruthStatus
    attributionReference : String
    evidenceReferences : List String
    resolverReference : String

record ApplicabilityResolutionReceipt : Set where
  constructor applicabilityResolutionReceipt
  field
    legalStatus : LegalStatusProduct
    resultingApplicability : ApplicabilityStatus
    typedMeetReference : String
    jurisdictionReference : String
    temporalReference : String
    authorityReference : String
    exceptionReference : String
    resolverReference : String

------------------------------------------------------------------------
-- Cross-axis no-collapse laws.
------------------------------------------------------------------------

data SemanticRoleDeterminesIdentity : Set where
data IdentityDeterminesOccurrence : Set where
data AntecedentCandidateDeterminesIdentity : Set where
data MentionDeterminesOccurrence : Set where
data AssertionDeterminesTruth : Set where
data CourtHoldingDeterminesUniversalTruth : Set where
data EvidenceDeterminesTruth : Set where
data LinguisticAgentDeterminesDutyBearer : Set where
data PatientDeterminesRightsBearer : Set where
data JurisdictionMentionDeterminesApplicability : Set where
data ApplicabilityDeterminesViolation : Set where
data ViolationDeterminesLiability : Set where
data ModalAuxiliaryDeterminesDeonticForce : Set where
data EmptyCandidateSetDeterminesAbsence : Set where

semanticRoleDoesNotDetermineIdentity : SemanticRoleDeterminesIdentity → ⊥
semanticRoleDoesNotDetermineIdentity ()

identityDoesNotDetermineOccurrence : IdentityDeterminesOccurrence → ⊥
identityDoesNotDetermineOccurrence ()

antecedentCandidateDoesNotDetermineIdentity : AntecedentCandidateDeterminesIdentity → ⊥
antecedentCandidateDoesNotDetermineIdentity ()

mentionDoesNotDetermineOccurrence : MentionDeterminesOccurrence → ⊥
mentionDoesNotDetermineOccurrence ()

assertionDoesNotDetermineTruth : AssertionDeterminesTruth → ⊥
assertionDoesNotDetermineTruth ()

courtHoldingDoesNotDetermineUniversalTruth : CourtHoldingDeterminesUniversalTruth → ⊥
courtHoldingDoesNotDetermineUniversalTruth ()

evidenceDoesNotDetermineTruth : EvidenceDeterminesTruth → ⊥
evidenceDoesNotDetermineTruth ()

linguisticAgentDoesNotDetermineDutyBearer : LinguisticAgentDeterminesDutyBearer → ⊥
linguisticAgentDoesNotDetermineDutyBearer ()

patientDoesNotDetermineRightsBearer : PatientDeterminesRightsBearer → ⊥
patientDoesNotDetermineRightsBearer ()

jurisdictionMentionDoesNotDetermineApplicability : JurisdictionMentionDeterminesApplicability → ⊥
jurisdictionMentionDoesNotDetermineApplicability ()

applicabilityDoesNotDetermineViolation : ApplicabilityDeterminesViolation → ⊥
applicabilityDoesNotDetermineViolation ()

violationDoesNotDetermineLiability : ViolationDeterminesLiability → ⊥
violationDoesNotDetermineLiability ()

modalAuxiliaryDoesNotDetermineDeonticForce : ModalAuxiliaryDeterminesDeonticForce → ⊥
modalAuxiliaryDoesNotDetermineDeonticForce ()

emptyCandidateSetDoesNotDetermineAbsence : EmptyCandidateSetDeterminesAbsence → ⊥
emptyCandidateSetDoesNotDetermineAbsence ()

------------------------------------------------------------------------
-- Admission remains a separate owner/currency.
------------------------------------------------------------------------

existingAdmissionCurrencyStillRequired :
  Admission.ParserCandidateAloneAuthorizesAdmission → ⊥
existingAdmissionCurrencyStillRequired =
  Admission.parserCandidateAloneCannotAuthorizeAdmission
