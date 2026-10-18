module DASHI.Wikimedia.WikidataOntologyDiagnosticS29BridgeExact where

-- WIKI-1 DASHI integration, not new attribution for JMD's Lean checker.
-- Original finite-KB diagnostic and repair definitions:
-- github.com/meta-introspector (JMD),
-- dashi_lean4/DASHI/output-final_aristotle/RequestProject/
-- Diagnostics.lean, ConstraintSuite.lean, RepairReview.lean.
--
-- This module types the observer/consumer boundary. It does NOT claim
-- an Agda proof of a Lean theorem, a kernel run, a live Wikidata check,
-- or authorization for a public edit.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using (List)
open import Data.Empty using (⊥)
open import DASHI.Cognition.PNF.SensibLawReviewWorkstationExact
  using (ReviewStatus; ReviewAction; nextStatus; pending; accepted;
         abstained; accept; abstain; openSource)

data OntologyGraphView : Set where
  fullStatements truthyRank scopedSlice : OntologyGraphView

data CheckerOwner : Set where
  finiteKbDiagnostics constraintSuite advisoryRepairReview : CheckerOwner

data DiagnosticDisposition : Set where
  violation warning noViolationInCheckedSlice undetermined inapplicable :
    DiagnosticDisposition

record SourcePinnedCheckerRun : Set where
  constructor source-pinned-checker-run
  field
    sourceRevisionRef : String
    sourceSnapshotDigestRef : String
    wikidataEntityRef : String
    graphView : OntologyGraphView
    sliceRef : String
    checkerOwner : CheckerOwner
    leanSourceCommitRef : String
    producerRunRef : String
    producerReceiptRef : String
    producerOutputDigestRef : String
    originalAttributionRef : String
    executedChecker : Bool
    executionIsTrue : executedChecker ≡ true
    createsSemanticAuthority : Bool
    semanticAuthorityFalse : createsSemanticAuthority ≡ false
    grantsEditAuthority : Bool
    editAuthorityFalse : grantsEditAuthority ≡ false

open SourcePinnedCheckerRun public

record DiagnosticWitness (run : SourcePinnedCheckerRun) : Set where
  constructor diagnostic-witness
  field
    ruleRef : String
    witnessRef : String
    nativeStatementRefs : List String
    contextualEvidenceRefs : List String
    disposition : DiagnosticDisposition
    admittedClaimTruth : Bool
    claimTruthFalse : admittedClaimTruth ≡ false

open DiagnosticWitness public

record RepairAdvice (run : SourcePinnedCheckerRun) : Set where
  constructor repair-advice
  field
    candidateRef : String
    sourceIssueRef : String
    proposedChangeRef : String
    modelBeforeRef : String
    modelAfterRef : String
    modelVerdictRef : String
    modifiesLiveWikidata : Bool
    modifiesLiveWikidataFalse : modifiesLiveWikidata ≡ false
    grantsPublicEditAuthority : Bool
    grantsPublicEditAuthorityFalse : grantsPublicEditAuthority ≡ false

open RepairAdvice public

record OntologyReviewProjection (run : SourcePinnedCheckerRun) : Set where
  constructor ontology-review-projection
  field
    consumerScopeRef : String
    reviewItemRef : String
    witnesses : List (DiagnosticWitness run)
    advisoryRepairs : List (RepairAdvice run)
    currentStatus : ReviewStatus
    requestedAction : ReviewAction
    resultingStatus : ReviewStatus
    s29ReducerAgreement :
      resultingStatus ≡ nextStatus currentStatus requestedAction
    sourcesRewritten : Bool
    sourcesRewrittenFalse : sourcesRewritten ≡ false
    createsClaimTruth : Bool
    createsClaimTruthFalse : createsClaimTruth ≡ false
    editsWikidata : Bool
    editsWikidataFalse : editsWikidata ≡ false

open OntologyReviewProjection public

-- Agda checks only the S29 action/status equations for this carrier;
-- an actual diagnostic still needs producer output and an execution receipt.
acceptIsWorkflowStatus :
  nextStatus pending accept ≡ accepted
acceptIsWorkflowStatus = refl

abstainKeepsExternalProofObligation :
  nextStatus pending abstain ≡ abstained
abstainKeepsExternalProofObligation = refl

navigationPreservesOntologyReviewStatus :
  ∀ {status} → nextStatus status openSource ≡ status
navigationPreservesOntologyReviewStatus = refl

-- A full-graph finite-KB check and a truthy-rank subset report are
-- different indexed objects; neither may stand for the other by default.
data DifferentGraphView : OntologyGraphView → OntologyGraphView → Set where
  fullVsTruthy : DifferentGraphView fullStatements truthyRank
  truthyVsFull : DifferentGraphView truthyRank fullStatements

-- Prohibitions define absent *implicit casts*, not a proof of source
-- or runtime completeness.
data TruthyReportSubstitutesFull : Set where
data FiniteCleanProvesGlobalConsistency : Set where
data LeanSourceCitationProvesExecution : Set where
data ModeledRepairAuthorizesPublicEdit : Set where
data AcceptedReviewGrantsEditAuthority : Set where
data SameIdentifierImpliesSemanticIdentity : Set where

cannotReplaceFullWithTruthy :
  TruthyReportSubstitutesFull → ⊥
cannotReplaceFullWithTruthy ()

finiteIsNotGlobal : FiniteCleanProvesGlobalConsistency → ⊥
finiteIsNotGlobal ()

sourceCitationIsNotExecution : LeanSourceCitationProvesExecution → ⊥
sourceCitationIsNotExecution ()

repairIsAdvisory : ModeledRepairAuthorizesPublicEdit → ⊥
repairIsAdvisory ()

reviewIsNotEditAuthority : AcceptedReviewGrantsEditAuthority → ⊥
reviewIsNotEditAuthority ()

identifierIsNotSemanticProof : SameIdentifierImpliesSemanticIdentity → ⊥
identifierIsNotSemanticProof ()
