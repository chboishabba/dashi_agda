module DASHI.Wikimedia.SLRP854ExternalReferenceInspectionABIExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.NativeReferenceSemanticsExact as Native
import DASHI.Wikimedia.NativeReferenceAttributedSourceBridgeExact as Attributed

------------------------------------------------------------------------
-- RESIDUAL-BOUND P854 EXTERNAL-REFERENCE INSPECTION ABI
--
-- This is the formal counterpart of the Rust SLR #10 external_reference module.
-- It does not add a fetcher.  It binds an already-classified P854 source
-- candidate to one exact live consumer residual/coordinate, then distinguishes
-- successful external-content inspection from no-match / blocked / failed
-- execution.  Inspection still does not pay source support by itself.
------------------------------------------------------------------------

record BoundP854InspectionDemand
    (candidate : Native.ReferenceSourceCandidate) : Set where
  constructor bound-p854-inspection-demand
  field
    consumerReference : String
    exactPrerequisiteReference : String
    requestedCoordinateReference : String
    requestIdentityReference : String
    statementReference : String
    p854URLReference : String
    referenceKindIsP854 :
      Native.referenceKind (Native.classified candidate)
      ≡ Native.referenceUrlReference

open BoundP854InspectionDemand public

data P854InspectionExecutionStatus : Set where
  executedWithOutput : P854InspectionExecutionStatus
  executedNoMatch : P854InspectionExecutionStatus
  blockedBeforeExecution : P854InspectionExecutionStatus
  providerUnavailable : P854InspectionExecutionStatus
  executionFailed : P854InspectionExecutionStatus

record InspectedP854ExternalSource
    {candidate : Native.ReferenceSourceCandidate}
    (demand : BoundP854InspectionDemand candidate) : Set where
  constructor inspected-p854-external-source
  field
    attributedSource : Attributed.AttributedReferenceSource candidate
    resultIdentityReference : String
    exactLocatorReference : String
    contentIdentityOrHashReference : String
    coverageReference : String
    uncertaintyReference : String
    provenanceReference : String
    sameURLAsP854Receipt : Set
    exactDemandPreservedReceipt : Set

open InspectedP854ExternalSource public

data P854InspectionResult {candidate : Native.ReferenceSourceCandidate}
    (demand : BoundP854InspectionDemand candidate) : Set where
  inspected : InspectedP854ExternalSource demand → P854InspectionResult demand
  noMatch : String → String → P854InspectionResult demand
  blocked : String → P854InspectionResult demand
  unavailable : String → P854InspectionResult demand
  failed : String → P854InspectionResult demand

executionStatus :
  ∀ {candidate} {demand : BoundP854InspectionDemand candidate} →
  P854InspectionResult demand → P854InspectionExecutionStatus
executionStatus (inspected _) = executedWithOutput
executionStatus (noMatch _ _) = executedNoMatch
executionStatus (blocked _) = blockedBeforeExecution
executionStatus (unavailable _) = providerUnavailable
executionStatus (failed _) = executionFailed

canEnterSemanticAssessment :
  ∀ {candidate} {demand : BoundP854InspectionDemand candidate} →
  P854InspectionResult demand → Bool
canEnterSemanticAssessment (inspected _) = true
canEnterSemanticAssessment (noMatch _ _) = false
canEnterSemanticAssessment (blocked _) = false
canEnterSemanticAssessment (unavailable _) = false
canEnterSemanticAssessment (failed _) = false

------------------------------------------------------------------------
-- Introspective / authority firewalls.
------------------------------------------------------------------------

data P854CandidatePaysSourceSupport : Set where
data P854FetchSuccessPaysSourceSupport : Set where
data P854NoMatchMeansPropositionFalse : Set where
data InspectedP854CreatesTruth : Set where
data InspectedP854CreatesApplicability : Set where

p854CandidateDoesNotPaySourceSupport : P854CandidatePaysSourceSupport → ⊥
p854CandidateDoesNotPaySourceSupport ()

p854FetchSuccessDoesNotPaySourceSupport : P854FetchSuccessPaysSourceSupport → ⊥
p854FetchSuccessDoesNotPaySourceSupport ()

p854NoMatchDoesNotMeanPropositionFalse : P854NoMatchMeansPropositionFalse → ⊥
p854NoMatchDoesNotMeanPropositionFalse ()

inspectedP854DoesNotCreateTruth : InspectedP854CreatesTruth → ⊥
inspectedP854DoesNotCreateTruth ()

inspectedP854DoesNotCreateApplicability : InspectedP854CreatesApplicability → ⊥
inspectedP854DoesNotCreateApplicability ()

record P854ExternalReferenceInspectionBoundary : Set where
  constructor p854-external-reference-inspection-boundary
  field
    demandIsBoundToExactLivePrerequisite : Bool
    demandIsBoundToExactLivePrerequisiteIsTrue :
      demandIsBoundToExactLivePrerequisite ≡ true
    p854CandidateRequiresExternalInspection : Bool
    p854CandidateRequiresExternalInspectionIsTrue :
      p854CandidateRequiresExternalInspection ≡ true
    inspectedOutputMayEnterSemanticAssessment : Bool
    inspectedOutputMayEnterSemanticAssessmentIsTrue :
      inspectedOutputMayEnterSemanticAssessment ≡ true
    noMatchMayEnterSemanticAssessment : Bool
    noMatchMayEnterSemanticAssessmentIsFalse :
      noMatchMayEnterSemanticAssessment ≡ false
    inspectedOutputPaysSourceSupportAutomatically : Bool
    inspectedOutputPaysSourceSupportAutomaticallyIsFalse :
      inspectedOutputPaysSourceSupportAutomatically ≡ false
    slrImplementationReference : String

canonicalP854ExternalReferenceInspectionBoundary :
  P854ExternalReferenceInspectionBoundary
canonicalP854ExternalReferenceInspectionBoundary =
  p854-external-reference-inspection-boundary
    true refl
    true refl
    true refl
    false refl
    false refl
    "chboishabba/slr PR #10 agent/source-unit-wikimedia-handoff commit 1eff189a40b1545e1ff3545cb9fa20f05748f1a0; crates/sl-source-handoff/src/external_reference.rs"
