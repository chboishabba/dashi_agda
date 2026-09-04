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

submittedRow : Spacy.NumericTokenRow
submittedRow = Spacy.numericTokenRow Reporting.submittedToken Spacy.rootCommit
conferredRow : Spacy.NumericTokenRow
conferredRow = Spacy.numericTokenRow Reporting.conferredToken (Spacy.dependencyCommit (Spacy.token Reporting.submittedToken))

pdfSyntacticProjection : Constitution.SyntacticProjectionReceipt
pdfSyntacticProjection = Constitution.syntacticProjectionReceipt submittedRow Constitution.complementRole "materialised PDF reporting predicate: submitted" true true true false
pdfStructuralComposition : Constitution.StructuralCompositionReceipt
pdfStructuralComposition = Constitution.structuralCompositionReceipt pdfSyntacticProjection (conferredRow ∷ []) (Constitution.reportingContentBoundary ∷ Constitution.sameSentence ∷ []) "same PDF nsubj+ccomp reporting/content composition" true false false
pdfConstitutionFibre : Constitution.SemanticCandidateFibre
pdfConstitutionFibre = Constitution.semanticCandidateFibre pdfStructuralComposition (Constitution.actorCandidate ∷ Constitution.unresolvedRelationCandidate ∷ []) true true

contextualProposition : Status.PropositionStatusProduct
contextualProposition = Document.ContextualPropositionRefinement.refined PdfDocument.contextualRefinement
contextualLegalStatus : Status.LegalStatusProduct
contextualLegalStatus = Document.ContextualLegalDiscourseProjection.legalStatus PdfDocument.legalDiscourseProjection
pdfPlannerState : Status.SemanticCommitmentState
pdfPlannerState = Status.semanticCommitmentState pdfConstitutionFibre [] (Reporting.sourceEventStatus ∷ []) (Reporting.sourceProposition ∷ contextualProposition ∷ []) (contextualLegalStatus ∷ []) true false

attributionActive = Demand.activeRequirement Consumer.generalSemanticConsumer Demand.whoSaidWhatQuery Demand.attributionCoordinate Demand.whoNeedsAttribution "PDF general who-said-what attribution"
propositionActive = Demand.activeRequirement Consumer.legalConsumer Demand.legalApplicabilityQuery Demand.propositionStatusCoordinate Demand.legalApplicabilityNeedsProposition "PDF applicability needs proposition status"
occurrenceActive = Demand.activeRequirement Consumer.legalConsumer Demand.legalApplicabilityQuery Demand.occurrenceCoordinate Demand.legalApplicabilityNeedsOccurrence "PDF applicability needs occurrence status"
documentContextActive = Demand.activeRequirement Consumer.legalConsumer Demand.legalApplicabilityQuery Demand.documentContextCoordinate Demand.legalApplicabilityNeedsContext "PDF applicability needs document/case context"
resolvedEvidenceActive = Demand.activeRequirement Consumer.legalConsumer Demand.legalApplicabilityQuery Demand.resolvedLegalEvidenceCoordinate Demand.legalApplicabilityNeedsResolvedEvidence "PDF applicability still requires same-object resolved legal-use evidence"
legalSourceAuthorityActive = Demand.activeRequirement Consumer.legalConsumer Demand.legalApplicabilityQuery Demand.legalSourceAuthorityCoordinate Demand.legalApplicabilityNeedsLegalSourceAuthority "PDF applicability still requires legal-source authority"
resolvedScopeActive = Demand.activeRequirement Consumer.legalConsumer Demand.legalApplicabilityQuery Demand.resolvedScopeCoordinate Demand.legalApplicabilityNeedsResolvedScope "PDF applicability still requires resolved same-object scope"
resolvedJurisdictionActive = Demand.activeRequirement Consumer.legalConsumer Demand.legalApplicabilityQuery Demand.resolvedLegalJurisdictionCoordinate Demand.legalApplicabilityNeedsResolvedJurisdiction "PDF applicability still requires resolved legal jurisdiction"

ownedProposition = Bridge.propositionReceiptInState Reporting.propositionReceipt Bridge.here "PDF PropositionResolutionReceipt is the first proposition in planner state"
ownedOccurrence = Bridge.occurrenceReceiptInState Reporting.occurrenceReceipt Bridge.here "PDF OccurrenceResolutionReceipt is the first event in planner state"
ownedAttribution = Bridge.attributionReceiptInState Reporting.propositionReceipt Bridge.here Bridge.propositionSourceResolved "PDF source proposition carries resolved proposition-source attribution"
ownedDocumentContext = Bridge.documentContextReceiptInState PdfDocument.applicantSubmissionFrame contextualProposition (Bridge.there Bridge.here) "PDF applicant-submission frame refines the second proposition in planner state"

attributionEvidence = Bridge.attributionReceiptPaysActiveCoordinate refl ownedAttribution
propositionEvidence = Bridge.propositionReceiptPaysActiveCoordinate refl ownedProposition
occurrenceEvidence = Bridge.occurrenceReceiptPaysActiveCoordinate refl ownedOccurrence
documentContextEvidence = Bridge.documentContextReceiptPaysActiveCoordinate refl ownedDocumentContext

attributionPlan = Planner.planRequirement attributionEvidence "reuse live PDF attribution"
propositionPlan = Planner.planRequirement propositionEvidence "reuse live PDF proposition status"
occurrencePlan = Planner.planRequirement occurrenceEvidence "reuse live PDF occurrence status"
documentContextPlan = Planner.planRequirement documentContextEvidence "reuse live PDF document context"

attributionReusesExisting : Planner.action attributionPlan ≡ Planner.reuseExisting
attributionReusesExisting = refl
propositionReusesExisting : Planner.action propositionPlan ≡ Planner.reuseExisting
propositionReusesExisting = refl
occurrenceReusesExisting : Planner.action occurrencePlan ≡ Planner.reuseExisting
occurrenceReusesExisting = refl
documentContextReusesExisting : Planner.action documentContextPlan ≡ Planner.reuseExisting
documentContextReusesExisting = refl

attributionWork = Routing.routedWork Routing.noProducerInvocation refl Routing.reuseWithoutProducer "attribution receipt already live"
propositionWork = Routing.routedWork Routing.noProducerInvocation refl Routing.reuseWithoutProducer "proposition receipt already live"
occurrenceWork = Routing.routedWork Routing.noProducerInvocation refl Routing.reuseWithoutProducer "occurrence receipt already live"
documentContextWork = Routing.routedWork Routing.noProducerInvocation refl Routing.reuseWithoutProducer "document context receipt already live"

resolvedEvidenceUnassessed = Planner.coordinateEvidenceReceipt Planner.currentUnassessed [] "source/proposition metadata is present, but no exact EvidenceItem/EventEvidenceLink legal-use evidence receipt has yet been produced for this PDF proposition/event" true refl true refl
resolvedEvidencePlan = Planner.planRequirement resolvedEvidenceUnassessed "inspect same-object legal-use evidence before applicability"
resolvedEvidenceNeedsInspection : Planner.action resolvedEvidencePlan ≡ Planner.inspectForEvidence
resolvedEvidenceNeedsInspection = refl
resolvedEvidenceWork = Routing.routedWork Routing.producerInvocationRequired refl (Routing.invokeProducer Routing.resolvedLegalEvidenceRoute) "inspect exact EvidenceItem/EventEvidenceLink/provenance receipt; do not promote parser or source evidence candidate"

legalSourceAuthorityUnassessed = Planner.coordinateEvidenceReceipt Planner.currentUnassessed [] "no legal-source authority search/verification receipt has yet been run for this PDF requirement" true refl true refl
legalSourceAuthorityPlan = Planner.planRequirement legalSourceAuthorityUnassessed "inspect legal-source authority before any missing classification"
legalSourceAuthorityNeedsInspection : Planner.action legalSourceAuthorityPlan ≡ Planner.inspectForEvidence
legalSourceAuthorityNeedsInspection = refl
legalSourceAuthorityWork = Routing.routedWork Routing.producerInvocationRequired refl (Routing.invokeProducer Routing.legalSourceAuthorityRoute) "inspect LegalSource/system/validity authority evidence"

resolvedScopeUnassessed = Planner.coordinateEvidenceReceipt Planner.currentUnassessed [] "no same-object joint ScopeCompositionReceipt has yet been produced for the PDF proposition/event" true refl true refl
resolvedScopePlan = Planner.planRequirement resolvedScopeUnassessed "inspect/resolve joint proposition scope before applicability"
resolvedScopeNeedsInspection : Planner.action resolvedScopePlan ≡ Planner.inspectForEvidence
resolvedScopeNeedsInspection = refl
resolvedScopeWork = Routing.routedWork Routing.producerInvocationRequired refl (Routing.invokeProducer Routing.resolvedScopeRoute) "inspect same-object joint scope resolution; do not route to parser scope candidate"

resolvedJurisdictionUnassessed = Planner.coordinateEvidenceReceipt Planner.currentUnassessed [] "document context does not itself establish the legal-system jurisdiction required for applicability" true refl true refl
resolvedJurisdictionPlan = Planner.planRequirement resolvedJurisdictionUnassessed "inspect CaseFrame/LegalSystem/resolved-jurisdiction evidence"
resolvedJurisdictionNeedsInspection : Planner.action resolvedJurisdictionPlan ≡ Planner.inspectForEvidence
resolvedJurisdictionNeedsInspection = refl
resolvedJurisdictionWork = Routing.routedWork Routing.producerInvocationRequired refl (Routing.invokeProducer Routing.resolvedLegalJurisdictionRoute) "inspect exact legal-system jurisdiction weld; do not promote geographic/document candidate"

data PdfParserReceiptPaysLegalSourceAuthorityRequirement : Set where
data PdfSourceEvidenceCandidatePaysResolvedLegalEvidence : Set where
data PdfParserScopeCandidatePaysResolvedScope : Set where
data PdfDocumentContextPaysResolvedLegalJurisdiction : Set where
data PaidPrefixMeansApplicabilityFullyResolved : Set where
data UnassessedResolvedEvidenceMeansMissing : Set where
data UnassessedLegalSourceAuthorityMeansMissing : Set where
data UnassessedResolvedScopeMeansMissing : Set where
data UnassessedResolvedJurisdictionMeansMissing : Set where

pdfParserDoesNotPayLegalSourceAuthority : PdfParserReceiptPaysLegalSourceAuthorityRequirement → ⊥
pdfParserDoesNotPayLegalSourceAuthority ()
pdfSourceEvidenceCandidateDoesNotPayResolvedLegalEvidence : PdfSourceEvidenceCandidatePaysResolvedLegalEvidence → ⊥
pdfSourceEvidenceCandidateDoesNotPayResolvedLegalEvidence ()
pdfParserScopeCandidateDoesNotPayResolvedScope : PdfParserScopeCandidatePaysResolvedScope → ⊥
pdfParserScopeCandidateDoesNotPayResolvedScope ()
pdfDocumentContextDoesNotPayResolvedLegalJurisdiction : PdfDocumentContextPaysResolvedLegalJurisdiction → ⊥
pdfDocumentContextDoesNotPayResolvedLegalJurisdiction ()
paidPrefixDoesNotMeanFullApplicability : PaidPrefixMeansApplicabilityFullyResolved → ⊥
paidPrefixDoesNotMeanFullApplicability ()
unassessedResolvedEvidenceDoesNotMeanMissing : UnassessedResolvedEvidenceMeansMissing → ⊥
unassessedResolvedEvidenceDoesNotMeanMissing ()
unassessedLegalSourceAuthorityDoesNotMeanMissing : UnassessedLegalSourceAuthorityMeansMissing → ⊥
unassessedLegalSourceAuthorityDoesNotMeanMissing ()
unassessedResolvedScopeDoesNotMeanMissing : UnassessedResolvedScopeMeansMissing → ⊥
unassessedResolvedScopeDoesNotMeanMissing ()
unassessedResolvedJurisdictionDoesNotMeanMissing : UnassessedResolvedJurisdictionMeansMissing → ⊥
unassessedResolvedJurisdictionDoesNotMeanMissing ()

record PdfPlannerLiveBoundary : Set where
  constructor pdf-planner-live-boundary
  field
    materialisedParserRowsReused propositionReceiptReused occurrenceReceiptReused attributionReceiptReused documentContextReceiptReused : Bool
    resolvedEvidenceIsUnassessed resolvedEvidenceRoutesToLegalEvidenceProducer : Bool
    legalSourceAuthorityIsUnassessed legalSourceAuthorityRoutesToInspectionProducer : Bool
    resolvedScopeIsUnassessed resolvedScopeRoutesToScopeResolutionProducer : Bool
    resolvedJurisdictionIsUnassessed resolvedJurisdictionRoutesToLegalJurisdictionProducer : Bool
    paidPrefixClosesApplicability plannerReparsesPdf : Bool
canonicalPdfPlannerLiveBoundary = pdf-planner-live-boundary true true true true true true true true true true true true true false false
