module DASHI.Cognition.PNF.SensibLawPdfActiveRequirementPlannerLiveExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SpacyNumericProjection as Spacy
import DASHI.Cognition.PNF.SensibLawSpacyCompositionOnlySemanticConstitutionExact as Constitution
import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status
import DASHI.Cognition.PNF.SensibLawPdfReportingAttributionMaterialisedLiveExact as Reporting
import DASHI.Cognition.PNF.SensibLawPdfReportingDocumentContextLiveExact as PdfDocument
import DASHI.Cognition.PNF.SensibLawDocumentDiscourseContextRefinementExact as Document
import DASHI.Cognition.PNF.SensibLawConsumerIndexedDiscourseInterpretationExact as Consumer
import DASHI.Cognition.PNF.SensibLawConsumerQuerySemanticCoordinateReopeningExact as Demand
import DASHI.Cognition.PNF.SensibLawActiveRequirementExecutionPlannerExact as Planner
import DASHI.Cognition.PNF.SensibLawLiveProducerCoordinateEvidenceBridgeExact as Bridge
import DASHI.Cognition.PNF.SensibLawRequirementProducerRoutingExact as Routing

------------------------------------------------------------------------
-- MATERIALISED PDF -> CONSTITUTION -> COMMITMENT STATE
------------------------------------------------------------------------

submittedRow : Spacy.NumericTokenRow
submittedRow = Spacy.numericTokenRow Reporting.submittedToken Spacy.rootCommit

conferredRow : Spacy.NumericTokenRow
conferredRow =
  Spacy.numericTokenRow Reporting.conferredToken
    (Spacy.dependencyCommit (Spacy.token Reporting.submittedToken))

pdfSyntacticProjection : Constitution.SyntacticProjectionReceipt
pdfSyntacticProjection =
  Constitution.syntacticProjectionReceipt
    submittedRow Constitution.complementRole
    "materialised PDF reporting predicate: submitted"
    true true true false

pdfStructuralComposition : Constitution.StructuralCompositionReceipt
pdfStructuralComposition =
  Constitution.structuralCompositionReceipt
    pdfSyntacticProjection
    (conferredRow ∷ [])
    (Constitution.reportingContentBoundary ∷ Constitution.sameSentence ∷ [])
    "same PDF nsubj+ccomp reporting/content composition"
    true false false

pdfConstitutionFibre : Constitution.SemanticCandidateFibre
pdfConstitutionFibre =
  Constitution.semanticCandidateFibre
    pdfStructuralComposition
    (Constitution.actorCandidate ∷ Constitution.unresolvedRelationCandidate ∷ [])
    true true

contextualProposition : Status.PropositionStatusProduct
contextualProposition =
  Document.ContextualPropositionRefinement.refined PdfDocument.contextualRefinement

contextualLegalStatus : Status.LegalStatusProduct
contextualLegalStatus =
  Document.ContextualLegalDiscourseProjection.legalStatus
    PdfDocument.legalDiscourseProjection

pdfPlannerState : Status.SemanticCommitmentState
pdfPlannerState =
  Status.semanticCommitmentState
    pdfConstitutionFibre []
    (Reporting.sourceEventStatus ∷ [])
    (Reporting.sourceProposition ∷ contextualProposition ∷ [])
    (contextualLegalStatus ∷ [])
    true false

------------------------------------------------------------------------
-- Active requirements.
------------------------------------------------------------------------

attributionActive : Demand.ActiveRequirement
attributionActive =
  Demand.activeRequirement Consumer.generalSemanticConsumer Demand.whoSaidWhatQuery
    Demand.attributionCoordinate Demand.whoNeedsAttribution
    "PDF general who-said-what attribution"

propositionActive : Demand.ActiveRequirement
propositionActive =
  Demand.activeRequirement Consumer.legalConsumer Demand.legalApplicabilityQuery
    Demand.propositionStatusCoordinate Demand.legalApplicabilityNeedsProposition
    "PDF applicability needs proposition status"

occurrenceActive : Demand.ActiveRequirement
occurrenceActive =
  Demand.activeRequirement Consumer.legalConsumer Demand.legalApplicabilityQuery
    Demand.occurrenceCoordinate Demand.legalApplicabilityNeedsOccurrence
    "PDF applicability needs occurrence status"

documentContextActive : Demand.ActiveRequirement
documentContextActive =
  Demand.activeRequirement Consumer.legalConsumer Demand.legalApplicabilityQuery
    Demand.documentContextCoordinate Demand.legalApplicabilityNeedsContext
    "PDF applicability needs document/case context"

legalSourceAuthorityActive : Demand.ActiveRequirement
legalSourceAuthorityActive =
  Demand.activeRequirement Consumer.legalConsumer Demand.legalApplicabilityQuery
    Demand.legalSourceAuthorityCoordinate Demand.legalApplicabilityNeedsLegalSourceAuthority
    "PDF applicability still requires legal-source authority"

------------------------------------------------------------------------
-- Same-object producer ownership in the current state.
------------------------------------------------------------------------

ownedProposition : Bridge.PropositionReceiptInState pdfPlannerState
ownedProposition =
  Bridge.propositionReceiptInState Reporting.propositionReceipt Bridge.here
    "PDF PropositionResolutionReceipt is the first proposition in planner state"

ownedOccurrence : Bridge.OccurrenceReceiptInState pdfPlannerState
ownedOccurrence =
  Bridge.occurrenceReceiptInState Reporting.occurrenceReceipt Bridge.here
    "PDF OccurrenceResolutionReceipt is the first event in planner state"

ownedAttribution : Bridge.AttributionReceiptInState pdfPlannerState
ownedAttribution =
  Bridge.attributionReceiptInState Reporting.propositionReceipt Bridge.here
    Bridge.propositionSourceResolved
    "PDF source proposition carries resolved proposition-source attribution"

ownedDocumentContext : Bridge.DocumentContextReceiptInState pdfPlannerState
ownedDocumentContext =
  Bridge.documentContextReceiptInState PdfDocument.applicantSubmissionFrame
    contextualProposition (Bridge.there Bridge.here)
    "PDF applicant-submission frame refines the second proposition in planner state"

------------------------------------------------------------------------
-- Paid producer receipts compile to reuse-existing plans.
------------------------------------------------------------------------

attributionEvidence : Planner.CoordinateEvidenceReceipt pdfPlannerState attributionActive
attributionEvidence = Bridge.attributionReceiptPaysActiveCoordinate refl ownedAttribution

propositionEvidence : Planner.CoordinateEvidenceReceipt pdfPlannerState propositionActive
propositionEvidence = Bridge.propositionReceiptPaysActiveCoordinate refl ownedProposition

occurrenceEvidence : Planner.CoordinateEvidenceReceipt pdfPlannerState occurrenceActive
occurrenceEvidence = Bridge.occurrenceReceiptPaysActiveCoordinate refl ownedOccurrence

documentContextEvidence : Planner.CoordinateEvidenceReceipt pdfPlannerState documentContextActive
documentContextEvidence = Bridge.documentContextReceiptPaysActiveCoordinate refl ownedDocumentContext

attributionPlan : Planner.RequirementPlan pdfPlannerState attributionActive
attributionPlan = Planner.planRequirement attributionEvidence "reuse live PDF attribution"
propositionPlan : Planner.RequirementPlan pdfPlannerState propositionActive
propositionPlan = Planner.planRequirement propositionEvidence "reuse live PDF proposition status"
occurrencePlan : Planner.RequirementPlan pdfPlannerState occurrenceActive
occurrencePlan = Planner.planRequirement occurrenceEvidence "reuse live PDF occurrence status"
documentContextPlan : Planner.RequirementPlan pdfPlannerState documentContextActive
documentContextPlan = Planner.planRequirement documentContextEvidence "reuse live PDF document context"

attributionReusesExisting : Planner.action attributionPlan ≡ Planner.reuseExisting
attributionReusesExisting = refl
propositionReusesExisting : Planner.action propositionPlan ≡ Planner.reuseExisting
propositionReusesExisting = refl
occurrenceReusesExisting : Planner.action occurrencePlan ≡ Planner.reuseExisting
occurrenceReusesExisting = refl
documentContextReusesExisting : Planner.action documentContextPlan ≡ Planner.reuseExisting
documentContextReusesExisting = refl

attributionWork : Routing.RoutedWork attributionPlan
attributionWork = Routing.routedWork Routing.noProducerInvocation refl Routing.reuseWithoutProducer "attribution receipt already live"
propositionWork : Routing.RoutedWork propositionPlan
propositionWork = Routing.routedWork Routing.noProducerInvocation refl Routing.reuseWithoutProducer "proposition receipt already live"
occurrenceWork : Routing.RoutedWork occurrencePlan
occurrenceWork = Routing.routedWork Routing.noProducerInvocation refl Routing.reuseWithoutProducer "occurrence receipt already live"
documentContextWork : Routing.RoutedWork documentContextPlan
documentContextWork = Routing.routedWork Routing.noProducerInvocation refl Routing.reuseWithoutProducer "document context receipt already live"

------------------------------------------------------------------------
-- Legal-source authority is active but unassessed, not proven missing.
------------------------------------------------------------------------

legalSourceAuthorityUnassessed :
  Planner.CoordinateEvidenceReceipt pdfPlannerState legalSourceAuthorityActive
legalSourceAuthorityUnassessed =
  Planner.coordinateEvidenceReceipt Planner.currentUnassessed []
    "no legal-source authority search/verification receipt has yet been run for this PDF requirement"
    true refl true refl

legalSourceAuthorityPlan :
  Planner.RequirementPlan pdfPlannerState legalSourceAuthorityActive
legalSourceAuthorityPlan =
  Planner.planRequirement legalSourceAuthorityUnassessed
    "inspect legal-source authority before any missing classification"

legalSourceAuthorityNeedsInspection :
  Planner.action legalSourceAuthorityPlan ≡ Planner.inspectForEvidence
legalSourceAuthorityNeedsInspection = refl

legalSourceAuthorityWork : Routing.RoutedWork legalSourceAuthorityPlan
legalSourceAuthorityWork =
  Routing.routedWork Routing.producerInvocationRequired refl
    (Routing.invokeProducer Routing.legalSourceAuthorityRoute)
    "inspect LegalSource/system/validity authority evidence"

------------------------------------------------------------------------
-- Boundaries.
------------------------------------------------------------------------

data PdfParserReceiptPaysLegalSourceAuthorityRequirement : Set where
data PaidPrefixMeansApplicabilityFullyResolved : Set where

data UnassessedLegalSourceAuthorityMeansMissing : Set where

pdfParserDoesNotPayLegalSourceAuthority :
  PdfParserReceiptPaysLegalSourceAuthorityRequirement → ⊥
pdfParserDoesNotPayLegalSourceAuthority ()

paidPrefixDoesNotMeanFullApplicability :
  PaidPrefixMeansApplicabilityFullyResolved → ⊥
paidPrefixDoesNotMeanFullApplicability ()

unassessedLegalSourceAuthorityDoesNotMeanMissing :
  UnassessedLegalSourceAuthorityMeansMissing → ⊥
unassessedLegalSourceAuthorityDoesNotMeanMissing ()

record PdfPlannerLiveBoundary : Set where
  constructor pdf-planner-live-boundary
  field
    materialisedParserRowsReused : Bool
    propositionReceiptReused : Bool
    occurrenceReceiptReused : Bool
    attributionReceiptReused : Bool
    documentContextReceiptReused : Bool
    legalSourceAuthorityIsUnassessed : Bool
    legalSourceAuthorityRoutesToInspectionProducer : Bool
    paidPrefixClosesLegalSourceAuthority : Bool
    plannerReparsesPdf : Bool

canonicalPdfPlannerLiveBoundary : PdfPlannerLiveBoundary
canonicalPdfPlannerLiveBoundary =
  pdf-planner-live-boundary true true true true true true true false false
