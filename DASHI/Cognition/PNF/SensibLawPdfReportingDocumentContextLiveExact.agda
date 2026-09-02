module DASHI.Cognition.PNF.SensibLawPdfReportingDocumentContextLiveExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawPdfReportingAttributionMaterialisedLiveExact as Reporting
import DASHI.Cognition.PNF.SensibLawDocumentDiscourseContextRefinementExact as Context
import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status
import DASHI.Interop.SensibLawOntologyTopology as Ontology

------------------------------------------------------------------------
-- PDF-BACKED REPORTING -> DOCUMENT DISCOURSE CONTEXT
--
-- This owner takes the already materialised reporting-attribution receipt and
-- places the same proposition/perspective/event into the typed document
-- discourse layer.  The fixture's reporting classification is candidate
-- evidence for an applicant-submission frame; it is not heading-text authority,
-- legal truth authority, or governed legal admission.
------------------------------------------------------------------------

pdfCaseFrame : Ontology.CaseFrame
pdfCaseFrame =
  Ontology.caseFrame
    (Ontology.stableId "case:pdf-native-title:source-context")
    (Ontology.stableId "legal-system:pdf-native-title:context-unresolved")
    (Ontology.stableId "issue:pdf-native-title:lease-exclusive-possession")
    (Ontology.Event.eventId Reporting.embeddedEvent ∷ [])

record CandidateDocumentFramePopulation : Set where
  constructor candidateDocumentFramePopulation
  field
    frame : Context.DocumentDiscourseFrame
    sourceClaim : Ontology.Claim
    samePerspective :
      Context.perspective frame ≡ Reporting.applicantPerspective
    roleCandidateOnly : Bool
    roleCandidateOnlyIsTrue : roleCandidateOnly ≡ true
    parserReceiptReference : String
    documentStructureReference : String
    governedAdmissionPresent : Bool
    governedAdmissionPresentIsFalse : governedAdmissionPresent ≡ false

open CandidateDocumentFramePopulation public

applicantSubmissionFrame : Context.DocumentDiscourseFrame
applicantSubmissionFrame =
  Context.documentDiscourseFrame
    pdfCaseFrame
    Reporting.applicantPerspective
    "paragraph:0:515/sentence:1/span:133:375"
    Context.applicantSubmission
    ( "reporting-attribution-fixture-v01: nsubj(submitted, applicant)"
    ∷ "reporting-attribution-fixture-v01: ccomp(submitted, conferred)"
    ∷ "source paragraph sha256:84eeb6e3b6900521796fd1d669b7f8b1998d652ce8fed0a98fc0486b01e2a01d"
    ∷ [])
    "candidate document discourse frame from materialised reporting composition; no heading/regex authority"
    false refl
    false refl

candidateFramePopulation : CandidateDocumentFramePopulation
candidateFramePopulation =
  candidateDocumentFramePopulation
    applicantSubmissionFrame
    Reporting.applicantClaim
    refl
    true refl
    "sensiblaw.reporting-attribution-fixture.v0_1"
    "three-sentence paragraph context retained; sentence 1 contains applicant reporting composition"
    false refl

contextualRefinement :
  Context.ContextualPropositionRefinement
    Reporting.sourceProposition applicantSubmissionFrame
contextualRefinement =
  Context.refinePropositionFromDocumentFrame
    Reporting.sourceProposition applicantSubmissionFrame

legalDiscourseProjection :
  Context.ContextualLegalDiscourseProjection applicantSubmissionFrame
legalDiscourseProjection =
  Context.projectDocumentFrameToLegalDiscourse applicantSubmissionFrame

samePropositionAfterDocumentRefinement :
  Status.propositionReference
    (Context.ContextualPropositionRefinement.refined contextualRefinement)
  ≡ Status.propositionReference Reporting.sourceProposition
samePropositionAfterDocumentRefinement = refl

submissionStatusFromTypedFrame :
  Status.propositionStatus
    (Context.ContextualPropositionRefinement.refined contextualRefinement)
  ≡ Status.assertedBySource
submissionStatusFromTypedFrame = refl

submissionAttributionIsSpeaker :
  Status.attribution
    (Context.ContextualPropositionRefinement.refined contextualRefinement)
  ≡ Status.speaker
submissionAttributionIsSpeaker = refl

submissionTruthStillUnresolved :
  Status.truthStatus
    (Context.ContextualPropositionRefinement.refined contextualRefinement)
  ≡ Status.truthUnresolved
submissionTruthStillUnresolved = refl

judicialDiscourseIsSubmissionCandidate :
  Status.judicialStatus
    (Context.ContextualLegalDiscourseProjection.legalStatus legalDiscourseProjection)
  ≡ Status.submission
judicialDiscourseIsSubmissionCandidate = refl

------------------------------------------------------------------------
-- Boundaries.  This is a candidate document-discourse population receipt.
------------------------------------------------------------------------

data ReportingCandidateAutomaticallyGovernedDocumentRole : Set where
data SubmissionFrameProvesClaimTrue : Set where
data SubmissionFrameAdmitsUnderlyingOccurrence : Set where

data SubmissionFrameAdmitsWrongTypeApplicability : Set where

reportingCandidateDoesNotGovernDocumentRole :
  ReportingCandidateAutomaticallyGovernedDocumentRole → ⊥
reportingCandidateDoesNotGovernDocumentRole ()

submissionFrameDoesNotProveTruth : SubmissionFrameProvesClaimTrue → ⊥
submissionFrameDoesNotProveTruth ()

submissionFrameDoesNotAdmitOccurrence :
  SubmissionFrameAdmitsUnderlyingOccurrence → ⊥
submissionFrameDoesNotAdmitOccurrence ()

submissionFrameDoesNotAdmitWrongTypeApplicability :
  SubmissionFrameAdmitsWrongTypeApplicability → ⊥
submissionFrameDoesNotAdmitWrongTypeApplicability ()
