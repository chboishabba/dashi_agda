module DASHI.Cognition.PNF.SensibLawDocumentDiscourseLiveVerticalExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Empty using (⊥)

import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status
import DASHI.Cognition.PNF.SensibLawClaimAtomOntologyVerticalSliceExact as Vertical
import DASHI.Cognition.PNF.SensibLawDocumentDiscourseContextRefinementExact as Context

------------------------------------------------------------------------
-- LIVE DOCUMENT-CONTEXT VERTICAL REGRESSION
--
-- The same source proposition is viewed first under a typed party-submission
-- frame and then under a typed court-finding frame.  No source text is reparsed
-- and no heading string chooses the role.
------------------------------------------------------------------------

dogCaseFrame : Ontology.CaseFrame
dogCaseFrame =
  Ontology.caseFrame
    (Ontology.stableId "case:dog-walk-fixture")
    (Ontology.stableId "legal-system:fixture")
    (Ontology.stableId "issue:dog-walk")
    (Ontology.Event.eventId Vertical.dogEvent ∷ [])

respondentSubmissionFrame : Context.DocumentDiscourseFrame
respondentSubmissionFrame =
  Context.documentDiscourseFrame
    dogCaseFrame
    Vertical.dogPerspective
    "region:respondent-submissions"
    Context.respondentSubmission
    ("typed section-role receipt" ∷ "case-frame membership" ∷ [])
    "document discourse resolver"
    false refl
    false refl

courtFindingFrame : Context.DocumentDiscourseFrame
courtFindingFrame =
  Context.documentDiscourseFrame
    dogCaseFrame
    Vertical.dogPerspective
    "region:court-findings"
    Context.courtFinding
    ("typed finding-section receipt" ∷ "case-frame membership" ∷ [])
    "document discourse resolver"
    false refl
    false refl

sourceProposition : Status.PropositionStatusProduct
sourceProposition =
  Vertical.CrossCarrierPropositionReceipt.refined Vertical.dogWalkedPropositionLive

submissionRefinement :
  Context.ContextualPropositionRefinement sourceProposition respondentSubmissionFrame
submissionRefinement =
  Context.refinePropositionFromDocumentFrame sourceProposition respondentSubmissionFrame

findingRefinement :
  Context.ContextualPropositionRefinement sourceProposition courtFindingFrame
findingRefinement =
  Context.refinePropositionFromDocumentFrame sourceProposition courtFindingFrame

submissionIsSubmission :
  Status.propositionStatus
    (Context.ContextualPropositionRefinement.refined submissionRefinement)
  ≡ Status.assertedBySource
submissionIsSubmission = refl

submissionTruthUnchanged :
  Status.truthStatus
    (Context.ContextualPropositionRefinement.refined submissionRefinement)
  ≡ Status.truthUnresolved
submissionTruthUnchanged = refl

findingIsFinding :
  Status.propositionStatus
    (Context.ContextualPropositionRefinement.refined findingRefinement)
  ≡ Status.foundAsFact
findingIsFinding = refl

findingTruthStillUnresolved :
  Status.truthStatus
    (Context.ContextualPropositionRefinement.refined findingRefinement)
  ≡ Status.truthUnresolved
findingTruthStillUnresolved = refl

submissionLegalProjection :
  Context.ContextualLegalDiscourseProjection respondentSubmissionFrame
submissionLegalProjection =
  Context.projectDocumentFrameToLegalDiscourse respondentSubmissionFrame

findingLegalProjection :
  Context.ContextualLegalDiscourseProjection courtFindingFrame
findingLegalProjection =
  Context.projectDocumentFrameToLegalDiscourse courtFindingFrame

submissionJudicialStatus :
  Status.judicialStatus
    (Context.ContextualLegalDiscourseProjection.legalStatus submissionLegalProjection)
  ≡ Status.submission
submissionJudicialStatus = refl

findingJudicialStatus :
  Status.judicialStatus
    (Context.ContextualLegalDiscourseProjection.legalStatus findingLegalProjection)
  ≡ Status.findingOfFact
findingJudicialStatus = refl

------------------------------------------------------------------------
-- Occurrence establishment is an extra payment beyond finding-context status.
------------------------------------------------------------------------

sourceEvent : Status.EventStatusProduct
sourceEvent =
  Status.eventStatusProduct
    "event:dog-walk"
    Status.assertedOccurrence
    Status.eventTime
    Status.scopeUnresolved

findingOccurrenceReceipt :
  Context.CourtFindingOccurrenceReceipt
    courtFindingFrame
    sourceEvent
    (Context.ContextualPropositionRefinement.refined findingRefinement)
findingOccurrenceReceipt =
  Context.courtFindingOccurrenceReceipt
    refl
    refl
    "event:dog-walk"
    refl
    ("finding evidence receipt" ∷ "same-event case-frame receipt" ∷ [])
    "court finding occurrence resolver"
    Status.occurrenceAdmitted
    refl

establishedEventFromFinding : Status.EventStatusProduct
establishedEventFromFinding =
  Status.eventStatusProduct
    (Context.CourtFindingOccurrenceReceipt.eventReference findingOccurrenceReceipt)
    (Context.CourtFindingOccurrenceReceipt.resultingOccurrence findingOccurrenceReceipt)
    Status.eventTime
    Status.scopeResolved

findingEstablishesOccurrenceOnlyViaReceipt :
  Status.occurrence establishedEventFromFinding ≡ Status.occurrenceAdmitted
findingEstablishesOccurrenceOnlyViaReceipt = refl

submissionDoesNotEstablishOccurrence :
  Status.occurrence sourceEvent ≡ Status.assertedOccurrence
submissionDoesNotEstablishOccurrence = refl

------------------------------------------------------------------------
-- Same proposition/event identity survives contextual refinement.
------------------------------------------------------------------------

submissionSameProposition :
  Status.propositionReference
    (Context.ContextualPropositionRefinement.refined submissionRefinement)
  ≡ Status.propositionReference sourceProposition
submissionSameProposition =
  Context.ContextualPropositionRefinement.samePropositionReference
    submissionRefinement

findingSameProposition :
  Status.propositionReference
    (Context.ContextualPropositionRefinement.refined findingRefinement)
  ≡ Status.propositionReference sourceProposition
findingSameProposition =
  Context.ContextualPropositionRefinement.samePropositionReference findingRefinement

------------------------------------------------------------------------
-- No context shortcut.
------------------------------------------------------------------------

data SubmissionBecomesFindingWithoutFrameChange : Set where

data FindingReceiptMakesUniversalTruth : Set where

submissionDoesNotBecomeFindingWithoutFrame :
  SubmissionBecomesFindingWithoutFrameChange → ⊥
submissionDoesNotBecomeFindingWithoutFrame ()

findingReceiptDoesNotMakeUniversalTruth :
  FindingReceiptMakesUniversalTruth → ⊥
findingReceiptDoesNotMakeUniversalTruth ()
