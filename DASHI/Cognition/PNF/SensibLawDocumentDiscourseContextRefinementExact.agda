module DASHI.Cognition.PNF.SensibLawDocumentDiscourseContextRefinementExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status

------------------------------------------------------------------------
-- TYPED DOCUMENT-DISCOURSE CONTEXT
--
-- Repository archaeology found case/perspective/region carriers but no typed
-- section-role owner for party submissions, findings, holdings, quoted material
-- and orders.  This adapter supplies that missing coordinate.  It never derives
-- the role from heading text; the role itself must arrive as typed evidence.
------------------------------------------------------------------------

data DocumentDiscourseRole : Set where
  applicantSubmission respondentSubmission witnessEvidence
  courtFinding courtHolding quotedMaterial proceduralOrder
  neutralNarrative unresolvedDiscourseRole : DocumentDiscourseRole

record DocumentDiscourseFrame : Set where
  constructor documentDiscourseFrame
  field
    caseFrame : Ontology.CaseFrame
    perspective : Ontology.Perspective
    regionReference : String
    role : DocumentDiscourseRole
    roleEvidenceReferences : List String
    resolverReference : String
    headingTextUsedAsSemanticAuthority : Bool
    headingTextUsedAsSemanticAuthorityIsFalse :
      headingTextUsedAsSemanticAuthority ≡ false
    regexUsedAsSemanticAuthority : Bool
    regexUsedAsSemanticAuthorityIsFalse : regexUsedAsSemanticAuthority ≡ false

open DocumentDiscourseFrame public

rolePropositionStatus : DocumentDiscourseRole → Status.PropositionStatus
rolePropositionStatus applicantSubmission = Status.assertedBySource
rolePropositionStatus respondentSubmission = Status.assertedBySource
rolePropositionStatus witnessEvidence = Status.assertedBySource
rolePropositionStatus courtFinding = Status.foundAsFact
rolePropositionStatus courtHolding = Status.heldByCourt
rolePropositionStatus quotedMaterial = Status.quotedReportedProposition
rolePropositionStatus proceduralOrder = Status.propositionRepresented
rolePropositionStatus neutralNarrative = Status.propositionRepresented
rolePropositionStatus unresolvedDiscourseRole = Status.propositionUnresolved

roleJudicialStatus : DocumentDiscourseRole → Status.JudicialDiscourseStatus
roleJudicialStatus applicantSubmission = Status.submission
roleJudicialStatus respondentSubmission = Status.submission
roleJudicialStatus witnessEvidence = Status.judicialStatusUnresolved
roleJudicialStatus courtFinding = Status.findingOfFact
roleJudicialStatus courtHolding = Status.holding
roleJudicialStatus quotedMaterial = Status.judicialStatusUnresolved
roleJudicialStatus proceduralOrder = Status.order
roleJudicialStatus neutralNarrative = Status.judicialStatusUnresolved
roleJudicialStatus unresolvedDiscourseRole = Status.judicialStatusUnresolved

roleAttribution : DocumentDiscourseRole → Status.AttributionRole
roleAttribution applicantSubmission = Status.speaker
roleAttribution respondentSubmission = Status.speaker
roleAttribution witnessEvidence = Status.speaker
roleAttribution courtFinding = Status.propositionSource
roleAttribution courtHolding = Status.propositionSource
roleAttribution quotedMaterial = Status.quotedSpeaker
roleAttribution proceduralOrder = Status.propositionSource
roleAttribution neutralNarrative = Status.attributionUnresolved
roleAttribution unresolvedDiscourseRole = Status.attributionUnresolved

record ContextualPropositionRefinement
    (source : Status.PropositionStatusProduct)
    (frame : DocumentDiscourseFrame) : Set where
  constructor contextualPropositionRefinement
  field
    refined : Status.PropositionStatusProduct
    samePropositionReference :
      Status.propositionReference refined ≡ Status.propositionReference source
    propositionStatusFromRole :
      Status.propositionStatus refined ≡ rolePropositionStatus (role frame)
    attributionFromRole :
      Status.attribution refined ≡ roleAttribution (role frame)
    truthPreserved :
      Status.truthStatus refined ≡ Status.truthStatus source
    contextEvidenceRetained : List String

open ContextualPropositionRefinement public

refinePropositionFromDocumentFrame :
  (source : Status.PropositionStatusProduct) →
  (frame : DocumentDiscourseFrame) →
  ContextualPropositionRefinement source frame
refinePropositionFromDocumentFrame source frame =
  contextualPropositionRefinement
    (Status.propositionStatusProduct
      (Status.propositionReference source)
      (rolePropositionStatus (role frame))
      (Status.truthStatus source)
      (roleAttribution (role frame))
      (Status.evidencePolarity source)
      (Status.evidenceKind source)
      (Status.modalityKind source)
      (Status.modalForce source)
      (Status.modalScope source))
    refl refl refl refl
    (roleEvidenceReferences frame)

record ContextualLegalDiscourseProjection
    (frame : DocumentDiscourseFrame) : Set where
  constructor contextualLegalDiscourseProjection
  field
    legalStatus : Status.LegalStatusProduct
    judicialStatusFromRole :
      Status.judicialStatus legalStatus ≡ roleJudicialStatus (role frame)

open ContextualLegalDiscourseProjection public

projectDocumentFrameToLegalDiscourse :
  (frame : DocumentDiscourseFrame) → ContextualLegalDiscourseProjection frame
projectDocumentFrameToLegalDiscourse frame =
  contextualLegalDiscourseProjection
    (Status.legalStatusProduct
      Status.jurisdictionUnresolved
      Status.authorityUnresolved
      Status.conditionUnresolved
      Status.applicabilityUnresolved
      Status.violationUnresolved
      Status.liabilityUnresolved
      Status.burdenKindUnresolved
      Status.standardUnresolved
      (roleJudicialStatus (role frame))
      Status.normativeRelationUnresolved)
    refl

------------------------------------------------------------------------
-- Finding/holding context still cannot rewrite occurrence by itself.  A
-- separate same-event receipt is needed for occurrence establishment.
------------------------------------------------------------------------

record CourtFindingOccurrenceReceipt
    (frame : DocumentDiscourseFrame)
    (event : Status.EventStatusProduct)
    (proposition : Status.PropositionStatusProduct) : Set where
  constructor courtFindingOccurrenceReceipt
  field
    frameIsFinding : role frame ≡ courtFinding
    propositionIsFinding :
      Status.propositionStatus proposition ≡ Status.foundAsFact
    eventReference : String
    sameEventReference : Status.eventReference event ≡ eventReference
    evidenceReferences : List String
    resolverReference : String
    resultingOccurrence : Status.OccurrenceStatus
    resultingOccurrenceIsAdmitted :
      resultingOccurrence ≡ Status.occurrenceAdmitted

open CourtFindingOccurrenceReceipt public

------------------------------------------------------------------------
-- Boundaries.
------------------------------------------------------------------------

data HeadingTextChoosesDiscourseRole : Set where
data SubmissionContextProvesTruth : Set where
data FindingContextAloneProvesOccurrence : Set where
data HoldingContextProvesUniversalTruth : Set where

data DocumentContextDeletesLocalEvidence : Set where

headingTextDoesNotChooseRole : HeadingTextChoosesDiscourseRole → ⊥
headingTextDoesNotChooseRole ()

submissionContextDoesNotProveTruth : SubmissionContextProvesTruth → ⊥
submissionContextDoesNotProveTruth ()

findingContextAloneDoesNotProveOccurrence : FindingContextAloneProvesOccurrence → ⊥
findingContextAloneDoesNotProveOccurrence ()

holdingContextDoesNotProveUniversalTruth : HoldingContextProvesUniversalTruth → ⊥
holdingContextDoesNotProveUniversalTruth ()

documentContextDoesNotDeleteLocalEvidence : DocumentContextDeletesLocalEvidence → ⊥
documentContextDoesNotDeleteLocalEvidence ()
