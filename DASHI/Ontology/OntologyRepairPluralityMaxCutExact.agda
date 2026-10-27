module DASHI.Ontology.OntologyRepairPluralityMaxCutExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Integer using (ℤ)

import DASHI.Cognition.PNF.ReopenableEvidenceFibre as Reopenable
import DASHI.Cognition.PNF.TypePressure as PNFPressure
import DASHI.Cognition.PNF.WikidataRepairProposal as Repair
open import DASHI.Ontology.EducationOntologyMappingSSSOMExact

------------------------------------------------------------------------
-- DASHI MAX-CUT CONVERGENCE OWNER
--
-- Existing owners remain authoritative for their own semantics:
--   * SSSOM-shaped interchange/provenance: EducationOntologyMappingSSSOMExact
--   * signed evidence pressure: TypePressure
--   * reopenability/refutation separation: ReopenableEvidenceFibre
--   * repair proposal authority: WikidataRepairProposal
--
-- This file only composes them.  It does not attribute PNF, plurality,
-- reopening or repair-governance semantics to Mapping Commons, lgbtDB,
-- Rosario, the OCTF, Peter, Ege, or any external source.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- HETEROGENEOUS / PLURAL EVIDENCE INSIDE THE EXISTING PNF ENVELOPE
------------------------------------------------------------------------

data EvidenceOrigin : Set where
  structuralOrigin : EvidenceOrigin
  mappingOrigin : EvidenceOrigin
  llmOrigin : EvidenceOrigin
  humanReviewOrigin : EvidenceOrigin
  externalOntologyOrigin : EvidenceOrigin

record PluralRepairEvidence : Set where
  constructor pluralRepairEvidence
  field
    origin : EvidenceOrigin
    evidenceReference : String
    provenanceReference : String
    evidenceScope : String

open PluralRepairEvidence public

PluralPressureContribution : String → String → Set
PluralPressureContribution subject candidate =
  PNFPressure.TypePressureContribution
    {Subject = String}
    {CandidateType = String}
    {Evidence = PluralRepairEvidence}
    subject candidate

PluralPressureEnvelope : String → String → Set
PluralPressureEnvelope subject candidate =
  PNFPressure.TypePressureEnvelope
    {Subject = String}
    {CandidateType = String}
    {Evidence = PluralRepairEvidence}
    subject candidate

mkPluralPressure :
  (subject candidate : String) →
  PluralRepairEvidence →
  ℤ →
  PluralPressureContribution subject candidate
mkPluralPressure subject candidate evidence pressure =
  PNFPressure.typePressureContribution
    evidence
    pressure
    (provenanceReference evidence)
    (evidenceScope evidence)

pluralEnvelopePressure :
  {subject candidate : String} →
  PluralPressureEnvelope subject candidate → ℤ
pluralEnvelopePressure = PNFPressure.envelopePressure

data PluralPressureTruthPermission : Set where

pluralPressureCannotPromoteTruth : PluralPressureTruthPermission → ⊥
pluralPressureCannotPromoteTruth ()

pluralPressureStillCannotAssertType :
  PNFPressure.TypePressurePromotionPermission → ⊥
pluralPressureStillCannotAssertType = PNFPressure.pressureAloneCannotAssertType

------------------------------------------------------------------------
-- FINDING -> REPAIR SUGGESTION ROUTING
--
-- This function chooses a review candidate operation.  It is not an edit
-- command and not a proof that the suggested operation is semantically correct.
------------------------------------------------------------------------

suggestedOperation : MappingReviewFinding → Repair.RepairOperation
suggestedOperation noObservedMappingConflict = Repair.holdForReview
suggestedOperation predicateTooStrong = Repair.underspecifyType
suggestedOperation sourceVersionDrift = Repair.holdForReview
suggestedOperation hierarchyConflict = Repair.removeBadSuperclass
suggestedOperation disjointnessConflict = Repair.holdForReview
suggestedOperation unresolvedMappingConflict = Repair.holdForReview

compileRepairSuggestion :
  Repair.RepairTarget →
  MappingReviewFinding →
  Repair.RepairEvidence →
  Repair.RepairProposal
compileRepairSuggestion target finding evidence =
  Repair.repairProposal target (suggestedOperation finding) evidence

compiledSuggestionPreservesOperation :
  (target : Repair.RepairTarget) →
  (finding : MappingReviewFinding) →
  (evidence : Repair.RepairEvidence) →
  Repair.operation (compileRepairSuggestion target finding evidence)
  ≡ suggestedOperation finding
compiledSuggestionPreservesOperation target finding evidence = refl

data SuggestedRepairMutationPermission : Set where

suggestionCannotAuthorizeMutation : SuggestedRepairMutationPermission → ⊥
suggestionCannotAuthorizeMutation ()

suggestionStillUsesReviewAuthority : Repair.RepairProposalAuthority
suggestionStillUsesReviewAuthority = Repair.proposalForReviewOnly

suggestionCannotAssertTruth :
  Repair.RepairProposalTruthPermission Repair.proposalForReviewOnly → ⊥
suggestionCannotAssertTruth = Repair.repairProposalCannotAssertOntologyTruth

------------------------------------------------------------------------
-- VERSION DRIFT -> REOPEN, NOT REFUTATION
------------------------------------------------------------------------

record VersionDriftObservation : Set where
  constructor versionDriftObservation
  field
    mapping : SSSOMMapping
    observedSubjectVersion : String
    currentSubjectVersion : String
    observedObjectVersion : String
    currentObjectVersion : String
    driftReceipt : String

open VersionDriftObservation public

data MappingReviewReopenState : Set where
  reopenForReview : MappingReviewReopenState

reopenOnVersionDrift : VersionDriftObservation → MappingReviewReopenState
reopenOnVersionDrift drift = reopenForReview

data VersionDriftRefutationPermission : Set where

driftCannotRefuteMapping : VersionDriftRefutationPermission → ⊥
driftCannotRefuteMapping ()

reweightingStillCannotRefute :
  Reopenable.ReweightingRefutationPermission → ⊥
reweightingStillCannotRefute = Reopenable.reweightingAloneCannotRefute

------------------------------------------------------------------------
-- BOUNDED SSSOM-SHAPED ROUND TRIP
--
-- This is a local carrier round trip, not a claim of full SSSOM parser/schema
-- conformance.  It proves that the fields supported by `SSSOMMapping` survive
-- projection to and reconstruction from the local interchange row exactly.
------------------------------------------------------------------------

record SSSOMCoreRow : Set where
  constructor sssomCoreRow
  field
    rowSubjectId : String
    rowPredicate : MappingPredicate
    rowObjectId : String
    rowJustification : MappingJustificationKind
    rowAuthorId : String
    rowReviewerId : String
    rowConfidence : Nat
    rowSubjectSource : String
    rowSubjectSourceVersion : String
    rowObjectSource : String
    rowObjectSourceVersion : String
    rowDate : String
    rowComment : String

open SSSOMCoreRow public

encodeCoreMapping : SSSOMMapping → SSSOMCoreRow
encodeCoreMapping mapping =
  sssomCoreRow
    (subjectId mapping)
    (mappingPredicate mapping)
    (objectId mapping)
    (mappingJustification mapping)
    (authorId mapping)
    (reviewerId mapping)
    (confidence mapping)
    (subjectSource mapping)
    (subjectSourceVersion mapping)
    (objectSource mapping)
    (objectSourceVersion mapping)
    (mappingDate mapping)
    (mappingComment mapping)

decodeCoreMapping : SSSOMCoreRow → SSSOMMapping
decodeCoreMapping row =
  sssomMapping
    (rowSubjectId row)
    (rowPredicate row)
    (rowObjectId row)
    (rowJustification row)
    (rowAuthorId row)
    (rowReviewerId row)
    (rowConfidence row)
    (rowSubjectSource row)
    (rowSubjectSourceVersion row)
    (rowObjectSource row)
    (rowObjectSourceVersion row)
    (rowDate row)
    (rowComment row)

decodeEncodeCoreMapping :
  (mapping : SSSOMMapping) →
  decodeCoreMapping (encodeCoreMapping mapping) ≡ mapping
decodeEncodeCoreMapping
  (sssomMapping
    subject predicate object justification author reviewer conf
    subjectSrc subjectVersion objectSrc objectVersion date comment) = refl

encodeDecodeCoreRow :
  (row : SSSOMCoreRow) →
  encodeCoreMapping (decodeCoreMapping row) ≡ row
encodeDecodeCoreRow
  (sssomCoreRow
    subject predicate object justification author reviewer conf
    subjectSrc subjectVersion objectSrc objectVersion date comment) = refl

------------------------------------------------------------------------
-- STATUS
------------------------------------------------------------------------

record OntologyRepairPluralityStatus : Set where
  constructor ontologyRepairPluralityStatus
  field
    heterogeneousEvidenceUsesExistingPNFEnvelope : Bool
    pluralityDoesNotPromoteTruth : Bool
    repairRoutingCompilesToExistingProposal : Bool
    repairRoutingIsSuggestionOnly : Bool
    versionDriftReopensWithoutRefutation : Bool
    localSSSOMCarrierRoundTrips : Bool
    fullSSSOMParserConformanceNotClaimed : Bool

    heterogeneousEvidenceUsesExistingPNFEnvelopeIsTrue :
      heterogeneousEvidenceUsesExistingPNFEnvelope ≡ true
    pluralityDoesNotPromoteTruthIsTrue : pluralityDoesNotPromoteTruth ≡ true
    repairRoutingCompilesToExistingProposalIsTrue :
      repairRoutingCompilesToExistingProposal ≡ true
    repairRoutingIsSuggestionOnlyIsTrue : repairRoutingIsSuggestionOnly ≡ true
    versionDriftReopensWithoutRefutationIsTrue :
      versionDriftReopensWithoutRefutation ≡ true
    localSSSOMCarrierRoundTripsIsTrue : localSSSOMCarrierRoundTrips ≡ true
    fullSSSOMParserConformanceNotClaimedIsTrue :
      fullSSSOMParserConformanceNotClaimed ≡ true

open OntologyRepairPluralityStatus public

canonicalOntologyRepairPluralityStatus : OntologyRepairPluralityStatus
canonicalOntologyRepairPluralityStatus =
  ontologyRepairPluralityStatus
    true true true true true true true
    refl refl refl refl refl refl refl
