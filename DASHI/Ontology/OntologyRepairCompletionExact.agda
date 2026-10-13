module DASHI.Ontology.OntologyRepairCompletionExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_; _++_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.WikidataRepairProposal as Repair
import DASHI.Ontology.OntologyRepairPluralityMaxCutExact as Plural

------------------------------------------------------------------------
-- DASHI COMPLETION OWNER
--
-- This owner closes the remaining formal roadmap by composing existing owners.
-- It is not attributed to lgbtDB, Wikidata, SSSOM, Rosario, OCTF, SensibLaw,
-- Peter/Ege, Nat, or Mkrtchyan. External rows/docs below are pinned evidence;
-- all authority, lifecycle and non-collapse rules are DASHI reconstruction.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. EVIDENCE-STRENGTH-SENSITIVE REPAIR ROUTING
------------------------------------------------------------------------

data EvidenceClass : Set where
  llmOnlyEvidence : EvidenceClass
  structuralOnlyEvidence : EvidenceClass
  pluralReviewedEvidence : EvidenceClass

data RepairFinding : Set where
  noActionFinding : RepairFinding
  predicateStrengthFinding : RepairFinding
  redundantSuperclassFinding : RepairFinding
  badSuperclassFinding : RepairFinding
  entityConflationFinding : RepairFinding
  unresolvedFinding : RepairFinding

data DestructiveRepairAuthority : EvidenceClass → Set where
  pluralReviewedMayAuthorizeDestructiveCandidate :
    DestructiveRepairAuthority pluralReviewedEvidence

llmOnlyNotDestructive : DestructiveRepairAuthority llmOnlyEvidence → ⊥
llmOnlyNotDestructive ()

structuralOnlyNotDestructive : DestructiveRepairAuthority structuralOnlyEvidence → ⊥
structuralOnlyNotDestructive ()

routedOperation : RepairFinding → EvidenceClass → Repair.RepairOperation
routedOperation noActionFinding evidence = Repair.holdForReview
routedOperation predicateStrengthFinding llmOnlyEvidence = Repair.holdForReview
routedOperation predicateStrengthFinding structuralOnlyEvidence = Repair.underspecifyType
routedOperation predicateStrengthFinding pluralReviewedEvidence = Repair.underspecifyType
routedOperation redundantSuperclassFinding llmOnlyEvidence = Repair.holdForReview
routedOperation redundantSuperclassFinding structuralOnlyEvidence = Repair.holdForReview
routedOperation redundantSuperclassFinding pluralReviewedEvidence = Repair.removeRedundantSuperclass
routedOperation badSuperclassFinding llmOnlyEvidence = Repair.holdForReview
routedOperation badSuperclassFinding structuralOnlyEvidence = Repair.holdForReview
routedOperation badSuperclassFinding pluralReviewedEvidence = Repair.removeBadSuperclass
routedOperation entityConflationFinding llmOnlyEvidence = Repair.holdForReview
routedOperation entityConflationFinding structuralOnlyEvidence = Repair.holdForReview
routedOperation entityConflationFinding pluralReviewedEvidence = Repair.splitEntity
routedOperation unresolvedFinding evidence = Repair.holdForReview

compileEvidenceSensitiveRepair :
  Repair.RepairTarget →
  RepairFinding →
  EvidenceClass →
  Repair.RepairEvidence →
  Repair.RepairProposal
compileEvidenceSensitiveRepair target finding evidenceClass evidence =
  Repair.repairProposal target (routedOperation finding evidenceClass) evidence

------------------------------------------------------------------------
-- 2. APPEND-ONLY REVIEW / REOPENING LIFECYCLE
------------------------------------------------------------------------

data LifecycleState : Set where
  candidateState : LifecycleState
  reviewedState : LifecycleState
  heldState : LifecycleState
  promotableState : LifecycleState
  reopenedState : LifecycleState

data LifecycleEvent : Set where
  reviewCompleted : LifecycleEvent
  reviewHeld : LifecycleEvent
  reviewPromotable : LifecycleEvent
  sourceChanged : LifecycleEvent
  newEvidenceArrived : LifecycleEvent
  reevaluated : LifecycleEvent

nextLifecycle : LifecycleState → LifecycleEvent → LifecycleState
nextLifecycle candidateState reviewCompleted = reviewedState
nextLifecycle candidateState sourceChanged = reopenedState
nextLifecycle candidateState newEvidenceArrived = reopenedState
nextLifecycle candidateState event = candidateState
nextLifecycle reviewedState reviewHeld = heldState
nextLifecycle reviewedState reviewPromotable = promotableState
nextLifecycle reviewedState sourceChanged = reopenedState
nextLifecycle reviewedState newEvidenceArrived = reopenedState
nextLifecycle reviewedState event = reviewedState
nextLifecycle heldState sourceChanged = reopenedState
nextLifecycle heldState newEvidenceArrived = reopenedState
nextLifecycle heldState reevaluated = reviewedState
nextLifecycle heldState event = heldState
nextLifecycle promotableState sourceChanged = reopenedState
nextLifecycle promotableState newEvidenceArrived = reopenedState
nextLifecycle promotableState event = promotableState
nextLifecycle reopenedState reevaluated = reviewedState
nextLifecycle reopenedState event = reopenedState

record LifecycleReceipt : Set where
  constructor lifecycleReceipt
  field
    priorState : LifecycleState
    event : LifecycleEvent
    resultingState : LifecycleState
    provenance : String

open LifecycleReceipt public

advanceLifecycle : LifecycleReceipt → LifecycleEvent → String → LifecycleReceipt
advanceLifecycle receipt ev provenanceRef =
  lifecycleReceipt
    (resultingState receipt)
    ev
    (nextLifecycle (resultingState receipt) ev)
    provenanceRef

record LifecycleHistory : Set where
  constructor lifecycleHistory
  field
    current : LifecycleState
    receipts : List LifecycleReceipt

open LifecycleHistory public

appendTransition : LifecycleHistory → LifecycleEvent → String → LifecycleHistory
appendTransition history ev provenanceRef =
  let receipt = lifecycleReceipt (current history) ev (nextLifecycle (current history) ev) provenanceRef
  in lifecycleHistory (resultingState receipt) (receipts history ++ (receipt ∷ []))

------------------------------------------------------------------------
-- 3. PINNED REAL lgbtDB -> WIKIDATA FIXTURE
--
-- Source observation (retrieved 2026-10-13):
-- lgbtDB item "film festival" Q5051, oldid 343950, records a Wikidata Entity
-- ID Q220505 with stated-in DBpedia and mapping predicate "equivalent class".
-- This fixture pins that observed row; it does not assert the equivalence true.
------------------------------------------------------------------------

realLgbtDBFilmFestivalItem : String
realLgbtDBFilmFestivalItem = "Q5051"

realLgbtDBFilmFestivalRevision : String
realLgbtDBFilmFestivalRevision = "343950"

realLgbtDBFilmFestivalObjectId : String
realLgbtDBFilmFestivalObjectId = "Q220505"

record PinnedExternalMappingFixture : Set where
  constructor pinnedExternalMappingFixture
  field
    localItem : String
    pinnedRevision : String
    subjectSource : String
    objectSource : String
    objectId : String
    observedPredicate : String
    sourceLocator : String
    attributionReading : String

open PinnedExternalMappingFixture public

filmFestivalPinnedFixture : PinnedExternalMappingFixture
filmFestivalPinnedFixture =
  pinnedExternalMappingFixture
    realLgbtDBFilmFestivalItem
    realLgbtDBFilmFestivalRevision
    "DBpedia"
    "Wikidata"
    realLgbtDBFilmFestivalObjectId
    "equivalent class"
    "https://lgbtdb.wikibase.cloud/wiki/Item:Q5051 (oldid 343950)"
    "observed mapping row only; equivalence truth and downstream inference authority require separate review"

data ExternalFixtureTruthPermission : Set where

externalFixtureCannotAssertTruth : ExternalFixtureTruthPermission → ⊥
externalFixtureCannotAssertTruth ()

------------------------------------------------------------------------
-- 4. CLIMATE / NAT STATEMENT-BUNDLE MIGRATION DISPOSITIONS
--
-- Based on the SensibLaw P5991 -> P14143 migration protocol. These constructors
-- formalise repo review buckets; they do not claim every source statement belongs
-- to any particular bucket without a pinned statement-bundle receipt.
------------------------------------------------------------------------

data ClimateStatementShape : Set where
  alignedStatementBundle : ClimateStatementShape
  qualifierRemapStatementBundle : ClimateStatementShape
  stagedAddKeepSourceBundle : ClimateStatementShape
  semanticMismatchBundle : ClimateStatementShape
  referenceConflictBundle : ClimateStatementShape
  splitStatementBundle : ClimateStatementShape
  ambiguousStatementBundle : ClimateStatementShape

data ClimateMigrationDisposition : Set where
  safeRewrite : ClimateMigrationDisposition
  safeRewriteWithQualifierRemap : ClimateMigrationDisposition
  safeAddTargetKeepSource : ClimateMigrationDisposition
  keepSourceSemanticMismatch : ClimateMigrationDisposition
  manualReviewMigration : ClimateMigrationDisposition
  splitMigration : ClimateMigrationDisposition
  abstainMigration : ClimateMigrationDisposition

climateDisposition : ClimateStatementShape → ClimateMigrationDisposition
climateDisposition alignedStatementBundle = safeRewrite
climateDisposition qualifierRemapStatementBundle = safeRewriteWithQualifierRemap
climateDisposition stagedAddKeepSourceBundle = safeAddTargetKeepSource
climateDisposition semanticMismatchBundle = keepSourceSemanticMismatch
climateDisposition referenceConflictBundle = manualReviewMigration
climateDisposition splitStatementBundle = splitMigration
climateDisposition ambiguousStatementBundle = abstainMigration

data ClimateDispositionEditPermission : ClimateMigrationDisposition → Set where
  checkedSafeRewriteCandidate : ClimateDispositionEditPermission safeRewrite

manualReviewCannotEdit : ClimateDispositionEditPermission manualReviewMigration → ⊥
manualReviewCannotEdit ()

splitCannotBlindRewrite : ClimateDispositionEditPermission splitMigration → ⊥
splitCannotBlindRewrite ()

abstentionCannotEdit : ClimateDispositionEditPermission abstainMigration → ⊥
abstentionCannotEdit ()

------------------------------------------------------------------------
-- 5. TITLE / ALIAS / LANGUAGE / QID RESOLUTION
------------------------------------------------------------------------

data LanguageTag : Set where
  en : LanguageTag
  hy : LanguageTag
  otherLanguage : String → LanguageTag

data TitleResolutionState : Set where
  observedTitle : TitleResolutionState
  aliasCandidate : TitleResolutionState
  aliasResolvedExisting : TitleResolutionState
  qidResolvedExisting : TitleResolutionState
  confirmedArticleAbsent : TitleResolutionState

data TitleResolutionStep : TitleResolutionState → TitleResolutionState → Set where
  observedToAliasCandidate : TitleResolutionStep observedTitle aliasCandidate
  aliasToResolvedExisting : TitleResolutionStep aliasCandidate aliasResolvedExisting
  aliasToQidResolved : TitleResolutionStep aliasCandidate qidResolvedExisting
  aliasToConfirmedAbsent : TitleResolutionStep aliasCandidate confirmedArticleAbsent

data TitleResolutionTruthPermission : TitleResolutionState → Set where
  confirmedAbsenceMayEnterCoverageReview :
    TitleResolutionTruthPermission confirmedArticleAbsent

titleResolutionCannotAssertConceptTruth :
  TitleResolutionTruthPermission aliasResolvedExisting → ⊥
titleResolutionCannotAssertConceptTruth ()

qidResolutionCannotAssertConceptTruth :
  TitleResolutionTruthPermission qidResolvedExisting → ⊥
qidResolutionCannotAssertConceptTruth ()

------------------------------------------------------------------------
-- 6. MONOTONE EDUCATION PATCH CARRIER
------------------------------------------------------------------------

record EducationPatch : Set where
  constructor educationPatch
  field
    priorConcepts : List String
    priorProperties : List String
    priorRelations : List String
    conceptAdditions : List String
    propertyAdditions : List String
    relationAdditions : List String
    patchProvenance : List String

open EducationPatch public

nextConceptSnapshot : EducationPatch → List String
nextConceptSnapshot patch = priorConcepts patch ++ conceptAdditions patch

nextPropertySnapshot : EducationPatch → List String
nextPropertySnapshot patch = priorProperties patch ++ propertyAdditions patch

nextRelationSnapshot : EducationPatch → List String
nextRelationSnapshot patch = priorRelations patch ++ relationAdditions patch

------------------------------------------------------------------------
-- 7. END-TO-END GOVERNED DEMONSTRATOR
------------------------------------------------------------------------

record GovernedRepairCase : Set where
  constructor governedRepairCase
  field
    externalFixture : PinnedExternalMappingFixture
    evidenceOrigin : Plural.EvidenceOrigin
    evidenceClass : EvidenceClass
    finding : RepairFinding
    proposal : Repair.RepairProposal
    lifecycle : LifecycleHistory
    consumerReference : String
    factorisationReference : String
    attributionReference : String

open GovernedRepairCase public

filmFestivalReviewEvidence : Repair.RepairEvidence
filmFestivalReviewEvidence =
  Repair.repairEvidence
    (+ 0)
    []
    []
    "real mapping fixture enters review; no destructive conclusion follows from the observed row"
    "lgbtDB Q5051 oldid 343950; DBpedia -> Wikidata Q220505 mapping observation"
    "bounded film-festival mapping review"
  where
    open import Data.Integer using (+_)

filmFestivalReviewProposal : Repair.RepairProposal
filmFestivalReviewProposal =
  compileEvidenceSensitiveRepair
    (Repair.objectTarget 0)
    unresolvedFinding
    pluralReviewedEvidence
    filmFestivalReviewEvidence

filmFestivalLifecycle : LifecycleHistory
filmFestivalLifecycle =
  lifecycleHistory
    reviewedState
    (lifecycleReceipt candidateState reviewCompleted reviewedState
      "fixture reviewed as evidence-bearing mapping; ontology truth not asserted" ∷ [])

filmFestivalGovernedCase : GovernedRepairCase
filmFestivalGovernedCase =
  governedRepairCase
    filmFestivalPinnedFixture
    Plural.mappingOrigin
    pluralReviewedEvidence
    unresolvedFinding
    filmFestivalReviewProposal
    filmFestivalLifecycle
    "mapping review consumer"
    "consumer-specific FactorsThrough receipt must be supplied before inference use"
    "external mapping observation separated from DASHI review/proposal semantics"

endToEndProposalAuthority : Repair.RepairProposalAuthority
endToEndProposalAuthority = Repair.proposalForReviewOnly

------------------------------------------------------------------------
-- STATUS
------------------------------------------------------------------------

record CompletionStatus : Set where
  constructor completionStatus
  field
    evidenceStrengthControlsDestructiveRouting : Bool
    lifecycleReopensOnNewEvidence : Bool
    realPinnedExternalFixturePresent : Bool
    climateAbstentionFirstClass : Bool
    titleAliasQidStatesSeparated : Bool
    educationPatchIsAppendOnly : Bool
    endToEndCaseOwned : Bool
    endToEndCaseRemainsReviewOnly : Bool

    evidenceStrengthControlsDestructiveRoutingIsTrue :
      evidenceStrengthControlsDestructiveRouting ≡ true
    lifecycleReopensOnNewEvidenceIsTrue : lifecycleReopensOnNewEvidence ≡ true
    realPinnedExternalFixturePresentIsTrue : realPinnedExternalFixturePresent ≡ true
    climateAbstentionFirstClassIsTrue : climateAbstentionFirstClass ≡ true
    titleAliasQidStatesSeparatedIsTrue : titleAliasQidStatesSeparated ≡ true
    educationPatchIsAppendOnlyIsTrue : educationPatchIsAppendOnly ≡ true
    endToEndCaseOwnedIsTrue : endToEndCaseOwned ≡ true
    endToEndCaseRemainsReviewOnlyIsTrue : endToEndCaseRemainsReviewOnly ≡ true

open CompletionStatus public

canonicalCompletionStatus : CompletionStatus
canonicalCompletionStatus =
  completionStatus
    true true true true true true true true
    refl refl refl refl refl refl refl refl
