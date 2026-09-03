module DASHI.Cognition.PNF.SensibLawLiveProducerCoordinateEvidenceBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status
import DASHI.Cognition.PNF.SensibLawConsumerQuerySemanticCoordinateReopeningExact as Demand
import DASHI.Cognition.PNF.SensibLawActiveRequirementExecutionPlannerExact as Planner
import DASHI.Cognition.PNF.SensibLawDocumentDiscourseContextRefinementExact as Document
import DASHI.Cognition.PNF.SensibLawScopeCompositionBidiExact as Scope

infix 4 _∈_
data _∈_ {A : Set} (x : A) : List A → Set where
  here : ∀ {xs} → x ∈ (x ∷ xs)
  there : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)

record PropositionReceiptInState (state : Status.SemanticCommitmentState) : Set where
  constructor propositionReceiptInState
  field
    receipt : Status.PropositionResolutionReceipt
    exactMembership : Status.proposition receipt ∈ Status.propositions state
    receiptReference : String
open PropositionReceiptInState public

record OccurrenceReceiptInState (state : Status.SemanticCommitmentState) : Set where
  constructor occurrenceReceiptInState
  field
    receipt : Status.OccurrenceResolutionReceipt
    exactMembership : Status.event receipt ∈ Status.events state
    receiptReference : String
open OccurrenceReceiptInState public

record ApplicabilityReceiptInState (state : Status.SemanticCommitmentState) : Set where
  constructor applicabilityReceiptInState
  field
    receipt : Status.ApplicabilityResolutionReceipt
    exactMembership : Status.legalStatus receipt ∈ Status.legalStatuses state
    receiptReference : String
open ApplicabilityReceiptInState public

record DocumentContextReceiptInState (state : Status.SemanticCommitmentState) : Set where
  constructor documentContextReceiptInState
  field
    frame : Document.DocumentDiscourseFrame
    refinedProposition : Status.PropositionStatusProduct
    propositionMembership : refinedProposition ∈ Status.propositions state
    frameReference : String
open DocumentContextReceiptInState public

data ResolvedAttribution : Status.AttributionRole → Set where
  authorResolved : ResolvedAttribution Status.author
  speakerResolved : ResolvedAttribution Status.speaker
  reporterResolved : ResolvedAttribution Status.reporter
  quotedSpeakerResolved : ResolvedAttribution Status.quotedSpeaker
  propositionSourceResolved : ResolvedAttribution Status.propositionSource

record AttributionReceiptInState (state : Status.SemanticCommitmentState) : Set where
  constructor attributionReceiptInState
  field
    propositionReceipt : Status.PropositionResolutionReceipt
    exactMembership : Status.proposition propositionReceipt ∈ Status.propositions state
    resolvedAttribution : ResolvedAttribution (Status.attribution (Status.proposition propositionReceipt))
    attributionReference : String
open AttributionReceiptInState public

record ResolvedScopeReceiptInState (state : Status.SemanticCommitmentState) : Set where
  constructor resolvedScopeReceiptInState
  field
    receipt : Scope.ScopeCompositionReceipt
    propositionMembership : Scope.proposition receipt ∈ Status.propositions state
    eventMembership : Scope.event receipt ∈ Status.events state
    modalScopeResolved : Scope.modalScope receipt ≡ Status.scopeResolved
    negationScopeResolved : Scope.negationScope receipt ≡ Status.scopeResolved
    conditionScopeResolved : Scope.conditionScope receipt ≡ Status.scopeResolved
    temporalScopeResolved : Scope.temporalScope receipt ≡ Status.scopeResolved
    scopeReference : String
open ResolvedScopeReceiptInState public

propositionReceiptPaysActiveCoordinate : ∀ {state active} → Demand.coordinate active ≡ Demand.propositionStatusCoordinate → PropositionReceiptInState state → Planner.CoordinateEvidenceReceipt state active
propositionReceiptPaysActiveCoordinate same owned = Planner.coordinateEvidenceReceipt Planner.currentResolved (PropositionReceiptInState.receiptReference owned ∷ []) "PropositionResolutionReceipt + exact current-state membership" true refl true refl

occurrenceReceiptPaysActiveCoordinate : ∀ {state active} → Demand.coordinate active ≡ Demand.occurrenceCoordinate → OccurrenceReceiptInState state → Planner.CoordinateEvidenceReceipt state active
occurrenceReceiptPaysActiveCoordinate same owned = Planner.coordinateEvidenceReceipt Planner.currentResolved (OccurrenceReceiptInState.receiptReference owned ∷ []) "OccurrenceResolutionReceipt + exact current-state membership" true refl true refl

attributionReceiptPaysActiveCoordinate : ∀ {state active} → Demand.coordinate active ≡ Demand.attributionCoordinate → AttributionReceiptInState state → Planner.CoordinateEvidenceReceipt state active
attributionReceiptPaysActiveCoordinate same owned = Planner.coordinateEvidenceReceipt Planner.currentResolved (AttributionReceiptInState.attributionReference owned ∷ []) "resolved attribution in PropositionResolutionReceipt + exact state membership" true refl true refl

resolvedScopeReceiptPaysActiveCoordinate : ∀ {state active} → Demand.coordinate active ≡ Demand.resolvedScopeCoordinate → ResolvedScopeReceiptInState state → Planner.CoordinateEvidenceReceipt state active
resolvedScopeReceiptPaysActiveCoordinate same owned = Planner.coordinateEvidenceReceipt Planner.currentResolved (ResolvedScopeReceiptInState.scopeReference owned ∷ []) "joint ScopeCompositionReceipt with all required scopes resolved + exact proposition/event membership" true refl true refl

applicabilityReceiptPaysActiveCoordinate : ∀ {state active} → Demand.coordinate active ≡ Demand.applicabilityCoordinate → ApplicabilityReceiptInState state → Planner.CoordinateEvidenceReceipt state active
applicabilityReceiptPaysActiveCoordinate same owned = Planner.coordinateEvidenceReceipt Planner.currentResolved (ApplicabilityReceiptInState.receiptReference owned ∷ []) "ApplicabilityResolutionReceipt + exact current-state membership" true refl true refl

documentContextReceiptPaysActiveCoordinate : ∀ {state active} → Demand.coordinate active ≡ Demand.documentContextCoordinate → DocumentContextReceiptInState state → Planner.CoordinateEvidenceReceipt state active
documentContextReceiptPaysActiveCoordinate same owned = Planner.coordinateEvidenceReceipt Planner.currentResolved (DocumentContextReceiptInState.frameReference owned ∷ []) "typed DocumentDiscourseFrame + exact contextual proposition membership" true refl true refl

record CoordinateSearchReceipt (state : Status.SemanticCommitmentState) (active : Demand.ActiveRequirement) : Set where
  constructor coordinateSearchReceipt
  field
    searchedCoordinate : Demand.SemanticCoordinate
    searchedCoordinateExact : searchedCoordinate ≡ Demand.coordinate active
    exhaustiveForCurrentScope : Bool
    exhaustiveForCurrentScopeIsTrue : exhaustiveForCurrentScope ≡ true
    evidenceReferences : List String
    searchReference : String
open CoordinateSearchReceipt public

missingAfterExhaustiveSearch : ∀ {state active} → CoordinateSearchReceipt state active → Planner.CoordinateEvidenceReceipt state active
missingAfterExhaustiveSearch searched = Planner.coordinateEvidenceReceipt Planner.currentMissing (CoordinateSearchReceipt.evidenceReferences searched) (CoordinateSearchReceipt.searchReference searched) true refl true refl

record CoordinateConflictReceipt (state : Status.SemanticCommitmentState) (active : Demand.ActiveRequirement) : Set where
  constructor coordinateConflictReceipt
  field
    leftEvidenceReferences : List String
    rightEvidenceReferences : List String
    conflictReference : String
    sameCoordinate : Bool
    sameCoordinateIsTrue : sameCoordinate ≡ true
open CoordinateConflictReceipt public

conflictReceiptProducesConflict : ∀ {state active} → CoordinateConflictReceipt state active → Planner.CoordinateEvidenceReceipt state active
conflictReceiptProducesConflict conflict = Planner.coordinateEvidenceReceipt Planner.currentConflicting (CoordinateConflictReceipt.leftEvidenceReferences conflict) (CoordinateConflictReceipt.conflictReference conflict) true refl true refl

record StaleCoordinateReceipt (state : Status.SemanticCommitmentState) (active : Demand.ActiveRequirement) : Set where
  constructor staleCoordinateReceipt
  field
    priorEvidenceReferences : List String
    changedDependencyReference : String
    staleReference : String
    wasPreviouslyResolved : Bool
    wasPreviouslyResolvedIsTrue : wasPreviouslyResolved ≡ true
open StaleCoordinateReceipt public

staleReceiptProducesReopening : ∀ {state active} → StaleCoordinateReceipt state active → Planner.CoordinateEvidenceReceipt state active
staleReceiptProducesReopening stale = Planner.coordinateEvidenceReceipt Planner.stalePreviouslyResolved (StaleCoordinateReceipt.priorEvidenceReferences stale) (StaleCoordinateReceipt.staleReference stale) true refl true refl

data ReceiptAboutOtherPropositionPaysRequirement : Set where
data ProducerTypeAlonePaysRequirement : Set where
data ParserCandidatePaysAuthorityCoordinate : Set where
data MissingEvidenceMayBeInferredFromNoLocalConstructor : Set where
data StaleEvidenceEqualsMissingEvidence : Set where
data UnresolvedAttributionCountsAsResolved : Set where
data ScopeReceiptForOtherEventPaysResolvedScope : Set where
data PartiallyResolvedScopePaysResolvedScope : Set where

otherPropositionReceiptDoesNotPay : ReceiptAboutOtherPropositionPaysRequirement → ⊥
otherPropositionReceiptDoesNotPay ()
producerTypeAloneDoesNotPay : ProducerTypeAlonePaysRequirement → ⊥
producerTypeAloneDoesNotPay ()
parserCandidateDoesNotPayAuthority : ParserCandidatePaysAuthorityCoordinate → ⊥
parserCandidateDoesNotPayAuthority ()
absenceOfConstructorDoesNotProveMissing : MissingEvidenceMayBeInferredFromNoLocalConstructor → ⊥
absenceOfConstructorDoesNotProveMissing ()
staleDoesNotCollapseToMissing : StaleEvidenceEqualsMissingEvidence → ⊥
staleDoesNotCollapseToMissing ()
unresolvedAttributionDoesNotCountAsResolved : UnresolvedAttributionCountsAsResolved → ⊥
unresolvedAttributionDoesNotCountAsResolved ()
otherEventScopeReceiptDoesNotPay : ScopeReceiptForOtherEventPaysResolvedScope → ⊥
otherEventScopeReceiptDoesNotPay ()
partialScopeDoesNotPayResolvedScope : PartiallyResolvedScopePaysResolvedScope → ⊥
partialScopeDoesNotPayResolvedScope ()

record LiveProducerCoordinateEvidenceBoundary : Set where
  constructor live-producer-coordinate-evidence-boundary
  field
    positiveReceiptRequiresExactStateMembership : Bool
    producerTypeAloneDischargesRequirement : Bool
    exhaustiveSearchRequiredForMissingClassification : Bool
    conflictingAndMissingRemainDistinct : Bool
    staleAndMissingRemainDistinct : Bool
    unresolvedAttributionCountsAsResolved : Bool
    resolvedScopeRequiresSamePropositionAndEvent : Bool
    resolvedScopeRequiresAllScopeAxesResolved : Bool
    parserCandidateMayPayAuthorityCoordinate : Bool
canonicalLiveProducerCoordinateEvidenceBoundary : LiveProducerCoordinateEvidenceBoundary
canonicalLiveProducerCoordinateEvidenceBoundary = live-producer-coordinate-evidence-boundary true false true true true false true true false
