module DASHI.Cognition.PNF.SensibLawPdfReportingDocumentContextLiveExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawPdfReportingAttributionMaterialisedLiveExact as Reporting
import DASHI.Cognition.PNF.SensibLawConsumerIndexedDiscourseInterpretationExact as Consumer
import DASHI.Cognition.PNF.SensibLawGenreSubjectDemandOrthogonalityExact as Axes
import DASHI.Cognition.PNF.SensibLawDocumentDiscourseContextRefinementExact as Context
import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status
import DASHI.Interop.SensibLawOntologyTopology as Ontology

pdfCaseFrame : Ontology.CaseFrame
pdfCaseFrame = Ontology.caseFrame
  (Ontology.stableId "case:pdf-native-title:source-context")
  (Ontology.stableId "legal-system:pdf-native-title:context-unresolved")
  (Ontology.stableId "issue:pdf-native-title:lease-exclusive-possession")
  (Ontology.Event.eventId Reporting.embeddedEvent ∷ [])

record CandidateDocumentFramePopulation : Set where
  constructor candidateDocumentFramePopulation
  field
    frame : Context.DocumentDiscourseFrame
    sourceClaim : Ontology.Claim
    samePerspective : Context.perspective frame ≡ Reporting.applicantPerspective
    roleCandidateOnly : Bool
    roleCandidateOnlyIsTrue : roleCandidateOnly ≡ true
    parserReceiptReference : String
    documentStructureReference : String
    governedAdmissionPresent : Bool
    governedAdmissionPresentIsFalse : governedAdmissionPresent ≡ false
open CandidateDocumentFramePopulation public

applicantSubmissionFrame : Context.DocumentDiscourseFrame
applicantSubmissionFrame = Context.documentDiscourseFrame pdfCaseFrame Reporting.applicantPerspective
  "paragraph:0:515/sentence:1/span:133:375" Context.applicantSubmission
  ("generic nsubj(submitted, applicant)" ∷ "generic clausalComplement(submitted, conferred)" ∷
   "source paragraph sha256:84eeb6e3b6900521796fd1d669b7f8b1998d652ce8fed0a98fc0486b01e2a01d" ∷ [])
  "candidate legal-context frame layered over existing general discourse carrier" false refl false refl

candidateFramePopulation : CandidateDocumentFramePopulation
candidateFramePopulation = candidateDocumentFramePopulation applicantSubmissionFrame Reporting.applicantClaim refl
  true refl "sensiblaw.reporting-attribution-fixture.v0_1"
  "three-sentence paragraph context retained; legal consumer supplies case/document role evidence"
  false refl

simultaneousDemand : Consumer.ConsumerDemandProfile
simultaneousDemand = Consumer.multiConsumerDemand
  ( Consumer.generalSemanticConsumer
  ∷ Consumer.legalConsumer
  ∷ Consumer.historicalConsumer
  ∷ Consumer.culturalConsumer
  ∷ [])
  (applicantSubmissionFrame ∷ [])
  "same PDF carrier requested simultaneously for general, legal, historical and cultural views"

multiInterpretation : Consumer.MultiConsumerDiscourseInterpretation
  Reporting.discourseCandidate Reporting.generalDiscourseResolution simultaneousDemand
multiInterpretation = Consumer.interpretForDemand Reporting.generalDiscourseResolution simultaneousDemand

sameUnderlyingCandidateAcrossConsumers :
  Consumer.underlyingCandidate multiInterpretation ≡ Reporting.discourseCandidate
sameUnderlyingCandidateAcrossConsumers = refl

parserNotRewrittenForConsumers : Consumer.parserRewrittenForConsumers multiInterpretation ≡ false
parserNotRewrittenForConsumers = refl

legalProjection : Consumer.LegalDiscourseProjection Reporting.generalDiscourseResolution applicantSubmissionFrame
legalProjection = Consumer.projectLegalDiscourse Reporting.generalDiscourseResolution applicantSubmissionFrame
legalProjectionPreservesGeneralTruth : Consumer.truthStatusPreserved legalProjection ≡ Status.truthUnresolved
legalProjectionPreservesGeneralTruth = refl
legalProjectionJudicialStatusIsSubmission : Consumer.legalJudicialStatus legalProjection ≡ Status.submission
legalProjectionJudicialStatusIsSubmission = refl

pdfTextProfile : Axes.TextContextProfile
pdfTextProfile = Axes.textContextProfile Axes.formalLegalDocument
  (Axes.legalSubject ∷ Axes.historicalSubject ∷ []) simultaneousDemand
  ("source provenance: legislation/case material fixture" ∷ [])
  ("native title/property law subject" ∷ "historical land tenure context" ∷ [])
  "formal legal source may still be consumed simultaneously through non-legal views"

contextualisedPdf : Axes.ContextualisedDiscourse Reporting.discourseCandidate Reporting.generalDiscourseResolution pdfTextProfile
contextualisedPdf = Axes.contextualise Reporting.generalDiscourseResolution pdfTextProfile

contextualRefinement : Context.ContextualPropositionRefinement Reporting.sourceProposition applicantSubmissionFrame
contextualRefinement = Context.refinePropositionFromDocumentFrame Reporting.sourceProposition applicantSubmissionFrame
legalDiscourseProjection : Context.ContextualLegalDiscourseProjection applicantSubmissionFrame
legalDiscourseProjection = Context.projectDocumentFrameToLegalDiscourse applicantSubmissionFrame
samePropositionAfterDocumentRefinement :
  Status.propositionReference (Context.ContextualPropositionRefinement.refined contextualRefinement)
  ≡ Status.propositionReference Reporting.sourceProposition
samePropositionAfterDocumentRefinement = refl
submissionTruthStillUnresolved :
  Status.truthStatus (Context.ContextualPropositionRefinement.refined contextualRefinement) ≡ Status.truthUnresolved
submissionTruthStillUnresolved = refl
judicialDiscourseIsSubmissionCandidate :
  Status.judicialStatus (Context.ContextualLegalDiscourseProjection.legalStatus legalDiscourseProjection) ≡ Status.submission
judicialDiscourseIsSubmissionCandidate = refl

data GeneralParseRequiresLegalInterpretation : Set where
data LegalContextChangesUnderlyingParse : Set where
data LegalVocabularyInTextAutomaticallySelectsLegalConsumer : Set where
data SubmissionFrameProvesClaimTrue : Set where
data OneConsumerErasesOtherRequestedViews : Set where

generalParseDoesNotRequireLegalInterpretation : GeneralParseRequiresLegalInterpretation → ⊥
generalParseDoesNotRequireLegalInterpretation ()
legalContextDoesNotChangeUnderlyingParse : LegalContextChangesUnderlyingParse → ⊥
legalContextDoesNotChangeUnderlyingParse ()
legalWordsDoNotAutomaticallySelectLegalConsumer : LegalVocabularyInTextAutomaticallySelectsLegalConsumer → ⊥
legalWordsDoNotAutomaticallySelectLegalConsumer ()
submissionFrameDoesNotProveTruth : SubmissionFrameProvesClaimTrue → ⊥
submissionFrameDoesNotProveTruth ()
oneConsumerDoesNotEraseOtherViews : OneConsumerErasesOtherRequestedViews → ⊥
oneConsumerDoesNotEraseOtherViews ()
