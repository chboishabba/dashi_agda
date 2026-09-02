module DASHI.Cognition.PNF.SensibLawPdfReportingDocumentContextLiveExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawPdfReportingAttributionMaterialisedLiveExact as Reporting
import DASHI.Cognition.PNF.SensibLawConsumerIndexedDiscourseInterpretationExact as Consumer
import DASHI.Cognition.PNF.SensibLawDocumentDiscourseContextRefinementExact as Context
import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status
import DASHI.Interop.SensibLawOntologyTopology as Ontology

------------------------------------------------------------------------
-- SAME GENERAL TEXT, OPTIONAL LEGAL-CONTEXT PROJECTION
--
-- The PDF-backed sentence already has a domain-neutral discourse parse.  A
-- legal consumer may additionally supply a typed case/document context and
-- obtain an applicant-submission projection.  The parser/discourse carrier is
-- shared literally; no legal mode reparses or overwrites the sentence.
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
    ( "generic nsubj(submitted, applicant)"
    ∷ "generic clausalComplement(submitted, conferred)"
    ∷ "source paragraph sha256:84eeb6e3b6900521796fd1d669b7f8b1998d652ce8fed0a98fc0486b01e2a01d"
    ∷ [])
    "candidate legal-context frame layered over existing general discourse carrier"
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
    "three-sentence paragraph context retained; legal consumer supplies case/document role evidence"
    false refl

------------------------------------------------------------------------
-- Two consumers over one literal general discourse candidate.
------------------------------------------------------------------------

generalInterpretation :
  Consumer.ConsumerIndexedDiscourseInterpretation
    Reporting.discourseCandidate Reporting.generalDiscourseResolution
generalInterpretation = Reporting.generalConsumerInterpretation

legalInterpretation :
  Consumer.ConsumerIndexedDiscourseInterpretation
    Reporting.discourseCandidate Reporting.generalDiscourseResolution
legalInterpretation =
  Consumer.legalContextInterpretation
    Reporting.generalDiscourseResolution applicantSubmissionFrame

sameUnderlyingCandidateAcrossConsumers :
  Consumer.underlyingCandidate generalInterpretation
  ≡ Consumer.underlyingCandidate legalInterpretation
sameUnderlyingCandidateAcrossConsumers = refl

parserNotRewrittenForGeneralConsumer :
  Consumer.parserRewrittenForConsumer generalInterpretation ≡ false
parserNotRewrittenForGeneralConsumer = refl

parserNotRewrittenForLegalConsumer :
  Consumer.parserRewrittenForConsumer legalInterpretation ≡ false
parserNotRewrittenForLegalConsumer = refl

legalProjection :
  Consumer.LegalDiscourseProjection
    Reporting.generalDiscourseResolution applicantSubmissionFrame
legalProjection =
  Consumer.projectLegalDiscourse
    Reporting.generalDiscourseResolution applicantSubmissionFrame

legalProjectionPreservesGeneralTruth :
  Consumer.truthStatusPreserved legalProjection ≡ Status.truthUnresolved
legalProjectionPreservesGeneralTruth = refl

legalProjectionJudicialStatusIsSubmission :
  Consumer.legalJudicialStatus legalProjection ≡ Status.submission
legalProjectionJudicialStatusIsSubmission = refl

------------------------------------------------------------------------
-- Existing proposition-level contextual projection remains available for legal
-- consumers and preserves the same proposition reference/truth coordinate.
------------------------------------------------------------------------

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
-- Boundaries.
------------------------------------------------------------------------

data GeneralParseRequiresLegalInterpretation : Set where
data LegalContextChangesUnderlyingParse : Set where
data LegalVocabularyInTextAutomaticallySelectsLegalConsumer : Set where
data SubmissionFrameProvesClaimTrue : Set where

generalParseDoesNotRequireLegalInterpretation :
  GeneralParseRequiresLegalInterpretation → ⊥
generalParseDoesNotRequireLegalInterpretation ()

legalContextDoesNotChangeUnderlyingParse :
  LegalContextChangesUnderlyingParse → ⊥
legalContextDoesNotChangeUnderlyingParse ()

legalWordsDoNotAutomaticallySelectLegalConsumer :
  LegalVocabularyInTextAutomaticallySelectsLegalConsumer → ⊥
legalWordsDoNotAutomaticallySelectLegalConsumer ()

submissionFrameDoesNotProveTruth : SubmissionFrameProvesClaimTrue → ⊥
submissionFrameDoesNotProveTruth ()
