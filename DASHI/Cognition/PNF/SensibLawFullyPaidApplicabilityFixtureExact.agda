module DASHI.Cognition.PNF.SensibLawFullyPaidApplicabilityFixtureExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Cognition.PNF.SensibLawPdfActiveRequirementPlannerLiveExact as PdfPlanner
import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status
import DASHI.Cognition.PNF.SensibLawClaimAtomOntologyVerticalSliceExact as Vertical
import DASHI.Cognition.PNF.SensibLawParticipantLegalRoleLiveBidiExact as LegalRoleLive
import DASHI.Cognition.PNF.SensibLawDocumentDiscourseContextRefinementExact as Document
import DASHI.Cognition.PNF.SensibLawScopeCompositionBidiExact as Scope
import DASHI.Reasoning.SpacyDependencyToCandidateLogicalPNFExact as Candidate
import DASHI.Cognition.PNF.SensibLawLiveProducerCoordinateEvidenceBridgeExact as Bridge
import DASHI.Cognition.PNF.SensibLawResolvedLegalEvidenceExact as Evidence
import DASHI.Cognition.PNF.SensibLawLegalSourceAuthorityEvidenceExact as Authority
import DASHI.Cognition.PNF.SensibLawLegalJurisdictionEvidenceExact as Jurisdiction
import DASHI.Cognition.PNF.SensibLawWrongTypeApplicabilityLiabilityRemedyBidiExact as Legal
import DASHI.Cognition.PNF.SensibLawApplicabilityPrerequisiteMeetExact as Meet
import DASHI.Cognition.PNF.SensibLawConsumerIndexedDiscourseInterpretationExact as Consumer
import DASHI.Cognition.PNF.SensibLawConsumerQuerySemanticCoordinateReopeningExact as Demand
import DASHI.Cognition.PNF.SensibLawActiveRequirementExecutionPlannerExact as Planner
import DASHI.Cognition.PNF.SensibLawRequirementProducerRoutingExact as Routing

------------------------------------------------------------------------
-- FULLY-PAID REGRESSION FIXTURE
--
-- This is a proof fixture, not a claim about real dog-walking law. It reuses
-- the existing canonical dog Event/Perspective/WrongType/system interpretation
-- and supplies one same-object graph of legal source, evidence, context, scope,
-- jurisdiction and legal-role receipts.
------------------------------------------------------------------------

fixtureSystem : Ontology.LegalSystem
fixtureSystem =
  Ontology.legalSystem
    LegalRoleLive.fixtureSystem
    (Ontology.stableId "legal-system:fixture-parent")
    "fixture-jurisdiction"
    "fixture regression system"

fixtureSource : Ontology.LegalSource
fixtureSource =
  Ontology.legalSource
    (Ontology.stableId "legal-source:fixture:dog-duty")
    LegalRoleLive.fixtureSystem
    Ontology.statute
    "Fixture Dog Duty Act s 1"
    "2026-01-01"
    "open"

fixtureCase : Ontology.CaseFrame
fixtureCase =
  Ontology.caseFrame
    (Ontology.stableId "case:fixture:dog-walk")
    LegalRoleLive.fixtureSystem
    (Ontology.stableId "issue:fixture:dog-duty")
    (Ontology.Event.eventId Vertical.dogEvent ∷ [])

fixtureDocumentFrame : Document.DocumentDiscourseFrame
fixtureDocumentFrame =
  Document.documentDiscourseFrame
    fixtureCase
    Vertical.dogPerspective
    "fixture:dog-walk/document-region"
    Document.applicantSubmission
    ("existing canonical dog-walk fixture" ∷ [])
    "fixture document-context resolver"
    false refl false refl

fixtureProposition : Status.PropositionStatusProduct
fixtureProposition =
  Status.propositionStatusProduct
    "dog-walked-positive"
    Status.assertedBySource
    Status.truthUnresolved
    Status.speaker
    Status.evidenceFor
    Status.documentaryEvidence
    Status.modalityKindUnresolved
    Status.modalForceUnresolved
    Status.scopeResolved

fixturePropositionReceipt : Status.PropositionResolutionReceipt
fixturePropositionReceipt =
  Status.propositionResolutionReceipt
    fixtureProposition
    Status.assertedBySource
    Status.truthUnresolved
    "actor:X"
    ("fixture documentary evidence" ∷ [])
    "same-object fixture proposition resolver"

fixtureEvent : Status.EventStatusProduct
fixtureEvent =
  Status.eventStatusProduct
    "event:dog-walk"
    Status.assertedOccurrence
    Status.eventTime
    Status.scopeResolved

fixtureOccurrenceReceipt : Status.OccurrenceResolutionReceipt
fixtureOccurrenceReceipt =
  Status.occurrenceResolutionReceipt
    fixtureEvent
    Status.assertedOccurrence
    ("dog-walked-positive" ∷ [])
    ("fixture documentary evidence" ∷ [])
    "same-object fixture occurrence resolver"

fixtureContextualRefinement :
  Document.ContextualPropositionRefinement fixtureProposition fixtureDocumentFrame
fixtureContextualRefinement =
  Document.refinePropositionFromDocumentFrame fixtureProposition fixtureDocumentFrame

fixtureContextProposition : Status.PropositionStatusProduct
fixtureContextProposition =
  Document.ContextualPropositionRefinement.refined fixtureContextualRefinement

contextCompilerReturnsExactProposition : fixtureContextProposition ≡ fixtureProposition
contextCompilerReturnsExactProposition = refl

fixtureLegalStatus : Status.LegalStatusProduct
fixtureLegalStatus =
  Status.legalStatusProduct
    Status.legalSystemJurisdiction
    Status.legalAuthority
    Status.conditionUnresolved
    Status.applicabilityCandidate
    Status.violationUnresolved
    Status.liabilityUnresolved
    Status.burdenKindUnresolved
    Status.standardUnresolved
    Status.submission
    Status.normativeRelationUnresolved

fixtureState : Status.SemanticCommitmentState
fixtureState =
  Status.semanticCommitmentState
    PdfPlanner.pdfConstitutionFibre
    (LegalRoleLive.dogSemanticSubject ∷ [])
    (fixtureEvent ∷ [])
    (fixtureProposition ∷ [])
    (fixtureLegalStatus ∷ [])
    true false

ownedProposition : Bridge.PropositionReceiptInState fixtureState
ownedProposition =
  Bridge.propositionReceiptInState fixturePropositionReceipt Bridge.here
    "fixture proposition exact state membership"

ownedOccurrence : Bridge.OccurrenceReceiptInState fixtureState
ownedOccurrence =
  Bridge.occurrenceReceiptInState fixtureOccurrenceReceipt Bridge.here
    "fixture event exact state membership"

ownedDocumentContext : Bridge.DocumentContextReceiptInState fixtureState
ownedDocumentContext =
  Bridge.documentContextReceiptInState fixtureDocumentFrame fixtureContextProposition Bridge.here
    "fixture applicant-submission context compiled to exact proposition"

ownedLegalRole : Bridge.LegalRoleReceiptInState fixtureState
ownedLegalRole =
  Bridge.legalRoleReceiptInState
    LegalRoleLive.fixtureDutyBearerWeld
    Bridge.here
    fixtureEvent
    Bridge.here
    refl
    "existing fixture duty-bearer weld over exact subject/event"

fixtureEvidenceItem : Ontology.EvidenceItem
fixtureEvidenceItem =
  Ontology.evidence
    (Ontology.stableId "evidence:fixture:dog-walk-document")
    "sha256:fixture-dog-walk-document"
    "text/plain"
    "2026-01-01"
    (Ontology.stableId "provenance:fixture:dog-walk-document")

fixtureEvidenceLink : Ontology.EventEvidenceLink
fixtureEvidenceLink =
  Ontology.attachEvidence Vertical.dogEvent fixtureEvidenceItem
    "supports asserted dog-walk proposition"

resolvedEvidence : Evidence.ResolvedLegalEvidenceReceiptInState fixtureState
resolvedEvidence =
  Evidence.resolvedLegalEvidenceReceiptInState
    fixtureEvidenceItem fixtureEvidenceLink fixtureEvent fixtureProposition
    Bridge.here Bridge.here refl refl
    Evidence.documentaryEvidenceLegalUse
    true refl
    ("provenance:fixture:dog-walk-document" ∷ [])
    "fixture resolved documentary evidence"

authorityReceipt : Authority.LegalSourceAuthorityReceiptInState fixtureState
authorityReceipt =
  Authority.legalSourceAuthorityReceiptInState
    fixtureSource fixtureSystem refl
    fixtureLegalStatus Bridge.here refl
    Authority.validityCurrent Authority.currentValidity
    ("Fixture Dog Duty Act s 1" ∷ [])
    ("fixture validity interval checked" ∷ [])
    ("fixture source recognized as legal authority" ∷ [])
    "fixture legal-source authority"

jurisdictionReceipt : Jurisdiction.LegalJurisdictionReceiptInState fixtureState
jurisdictionReceipt =
  Jurisdiction.legalJurisdictionReceiptInState
    fixtureCase fixtureSystem refl
    fixtureLegalStatus Bridge.here Jurisdiction.legalSystemResolved
    ("fixture case legal-system identity" ∷ [])
    ("fixture legal system record" ∷ [])
    "fixture resolved legal-system jurisdiction"

fixtureScopeBody : Candidate.Formula
fixtureScopeBody =
  Candidate.atom "Walk"
    (Candidate.eventTerm "event:dog-walk" ∷
     Candidate.entityTerm "actor:X" ∷ [])

fixtureScopeReceipt : Scope.ScopeCompositionReceipt
fixtureScopeReceipt =
  Scope.scopeCompositionReceipt
    fixtureProposition fixtureEvent fixtureScopeBody []
    Status.modalityKindUnresolved Status.modalForceUnresolved
    Status.scopeResolved Status.scopeResolved
    Status.conditionUnresolved Status.scopeResolved
    Status.eventTime Status.scopeResolved
    "fixture joint scope resolution" false false

ownedScope : Bridge.ResolvedScopeReceiptInState fixtureState
ownedScope =
  Bridge.resolvedScopeReceiptInState
    fixtureScopeReceipt Bridge.here Bridge.here
    refl refl refl refl
    "fixture same-object resolved scope"

prerequisites : Meet.ApplicabilityPrerequisiteBundle fixtureState
prerequisites =
  Meet.applicabilityPrerequisiteBundle
    ownedProposition ownedOccurrence ownedDocumentContext
    resolvedEvidence authorityReceipt jurisdictionReceipt ownedScope
    refl refl contextCompilerReturnsExactProposition refl refl refl refl
    "fully-paid fixture same-object prerequisite bundle"

------------------------------------------------------------------------
-- Applicability query: all seven requirements are already paid.
------------------------------------------------------------------------

propositionActive : Demand.ActiveRequirement
propositionActive = Demand.activeRequirement Consumer.legalConsumer Demand.legalApplicabilityQuery
  Demand.propositionStatusCoordinate Demand.legalApplicabilityNeedsProposition "fully-paid fixture proposition"
occurrenceActive : Demand.ActiveRequirement
occurrenceActive = Demand.activeRequirement Consumer.legalConsumer Demand.legalApplicabilityQuery
  Demand.occurrenceCoordinate Demand.legalApplicabilityNeedsOccurrence "fully-paid fixture occurrence"
documentContextActive : Demand.ActiveRequirement
documentContextActive = Demand.activeRequirement Consumer.legalConsumer Demand.legalApplicabilityQuery
  Demand.documentContextCoordinate Demand.legalApplicabilityNeedsContext "fully-paid fixture document context"
resolvedEvidenceActive : Demand.ActiveRequirement
resolvedEvidenceActive = Demand.activeRequirement Consumer.legalConsumer Demand.legalApplicabilityQuery
  Demand.resolvedLegalEvidenceCoordinate Demand.legalApplicabilityNeedsResolvedEvidence "fully-paid fixture resolved evidence"
legalSourceAuthorityActive : Demand.ActiveRequirement
legalSourceAuthorityActive = Demand.activeRequirement Consumer.legalConsumer Demand.legalApplicabilityQuery
  Demand.legalSourceAuthorityCoordinate Demand.legalApplicabilityNeedsLegalSourceAuthority "fully-paid fixture legal-source authority"
resolvedJurisdictionActive : Demand.ActiveRequirement
resolvedJurisdictionActive = Demand.activeRequirement Consumer.legalConsumer Demand.legalApplicabilityQuery
  Demand.resolvedLegalJurisdictionCoordinate Demand.legalApplicabilityNeedsResolvedJurisdiction "fully-paid fixture resolved jurisdiction"
resolvedScopeActive : Demand.ActiveRequirement
resolvedScopeActive = Demand.activeRequirement Consumer.legalConsumer Demand.legalApplicabilityQuery
  Demand.resolvedScopeCoordinate Demand.legalApplicabilityNeedsResolvedScope "fully-paid fixture resolved scope"

propositionEvidence = Bridge.propositionReceiptPaysActiveCoordinate refl ownedProposition
occurrenceEvidence = Bridge.occurrenceReceiptPaysActiveCoordinate refl ownedOccurrence
documentContextEvidence = Bridge.documentContextReceiptPaysActiveCoordinate refl ownedDocumentContext
resolvedEvidenceEvidence = Evidence.resolvedLegalEvidencePaysActiveCoordinate refl resolvedEvidence
legalSourceAuthorityEvidence = Authority.legalSourceAuthorityPaysActiveCoordinate refl authorityReceipt
resolvedJurisdictionEvidence = Jurisdiction.legalJurisdictionPaysActiveCoordinate refl jurisdictionReceipt
resolvedScopeEvidence = Bridge.resolvedScopeReceiptPaysActiveCoordinate refl ownedScope

propositionPlan = Planner.planRequirement propositionEvidence "reuse paid proposition"
occurrencePlan = Planner.planRequirement occurrenceEvidence "reuse paid occurrence"
documentContextPlan = Planner.planRequirement documentContextEvidence "reuse paid document context"
resolvedEvidencePlan = Planner.planRequirement resolvedEvidenceEvidence "reuse paid legal evidence"
legalSourceAuthorityPlan = Planner.planRequirement legalSourceAuthorityEvidence "reuse paid legal authority"
resolvedJurisdictionPlan = Planner.planRequirement resolvedJurisdictionEvidence "reuse paid jurisdiction"
resolvedScopePlan = Planner.planRequirement resolvedScopeEvidence "reuse paid scope"

propositionReuses : Planner.action propositionPlan ≡ Planner.reuseExisting
propositionReuses = refl
occurrenceReuses : Planner.action occurrencePlan ≡ Planner.reuseExisting
occurrenceReuses = refl
documentContextReuses : Planner.action documentContextPlan ≡ Planner.reuseExisting
documentContextReuses = refl
resolvedEvidenceReuses : Planner.action resolvedEvidencePlan ≡ Planner.reuseExisting
resolvedEvidenceReuses = refl
legalSourceAuthorityReuses : Planner.action legalSourceAuthorityPlan ≡ Planner.reuseExisting
legalSourceAuthorityReuses = refl
resolvedJurisdictionReuses : Planner.action resolvedJurisdictionPlan ≡ Planner.reuseExisting
resolvedJurisdictionReuses = refl
resolvedScopeReuses : Planner.action resolvedScopePlan ≡ Planner.reuseExisting
resolvedScopeReuses = refl

propositionWork = Routing.routedWork Routing.noProducerInvocation refl Routing.reuseWithoutProducer "paid proposition"
occurrenceWork = Routing.routedWork Routing.noProducerInvocation refl Routing.reuseWithoutProducer "paid occurrence"
documentContextWork = Routing.routedWork Routing.noProducerInvocation refl Routing.reuseWithoutProducer "paid document context"
resolvedEvidenceWork = Routing.routedWork Routing.noProducerInvocation refl Routing.reuseWithoutProducer "paid legal evidence"
legalSourceAuthorityWork = Routing.routedWork Routing.noProducerInvocation refl Routing.reuseWithoutProducer "paid legal authority"
resolvedJurisdictionWork = Routing.routedWork Routing.noProducerInvocation refl Routing.reuseWithoutProducer "paid jurisdiction"
resolvedScopeWork = Routing.routedWork Routing.noProducerInvocation refl Routing.reuseWithoutProducer "paid scope"

semanticInput : Legal.SemanticLegalInputGate Vertical.dogEvent
semanticInput = Legal.semanticLegalInputGate fixtureEvent fixtureProposition refl
  Status.applicabilityCandidate Legal.assertionCandidateUse

meetInput : Meet.ApplicabilityMeetInput fixtureState
meetInput =
  Meet.applicabilityMeetInput
    prerequisites Vertical.dogEvent
    LegalRoleLive.fixtureWrongType LegalRoleLive.fixtureInterpretation
    semanticInput fixtureLegalStatus Bridge.here
    refl refl refl refl refl refl
    "fully-paid same-object fixture typed meet"
    "fixture event time"
    "fixture exceptions checked"

compiledApplicability : Legal.WrongTypeApplicabilityReceipt
compiledApplicability = Meet.compileApplicabilityMeet meetInput

compiledApplicabilityIsStillCandidate :
  Legal.resultingApplicability compiledApplicability ≡ Status.applicabilityCandidate
compiledApplicabilityIsStillCandidate = refl

------------------------------------------------------------------------
-- Compile the paid meet into the reusable applicability currency.
------------------------------------------------------------------------

applicabilityResolution : Status.ApplicabilityResolutionReceipt
applicabilityResolution =
  Status.applicabilityResolutionReceipt
    fixtureLegalStatus
    Status.applicabilityCandidate
    "fully-paid same-object applicability meet"
    (Jurisdiction.jurisdictionReference jurisdictionReceipt)
    "fixture event time"
    (Authority.authorityReference authorityReceipt)
    "fixture exceptions checked"
    "ApplicabilityPrerequisiteMeetExact.compileApplicabilityMeet"

ownedApplicability : Bridge.ApplicabilityReceiptInState fixtureState
ownedApplicability =
  Bridge.applicabilityReceiptInState applicabilityResolution Bridge.here
    "compiled applicability receipt retained in same state"

------------------------------------------------------------------------
-- Liability query: previously-paid axes are reused; violation is the new cut.
------------------------------------------------------------------------

liabilityApplicabilityActive : Demand.ActiveRequirement
liabilityApplicabilityActive = Demand.activeRequirement Consumer.legalConsumer Demand.legalLiabilityQuery
  Demand.applicabilityCoordinate Demand.legalLiabilityNeedsApplicability "liability needs paid applicability"
liabilityViolationActive : Demand.ActiveRequirement
liabilityViolationActive = Demand.activeRequirement Consumer.legalConsumer Demand.legalLiabilityQuery
  Demand.violationCoordinate Demand.legalLiabilityNeedsViolation "liability still requires violation evaluation"
liabilityLegalRoleActive : Demand.ActiveRequirement
liabilityLegalRoleActive = Demand.activeRequirement Consumer.legalConsumer Demand.legalLiabilityQuery
  Demand.legalRoleCoordinate Demand.legalLiabilityNeedsLegalRole "liability needs resolved legal role"
liabilityEvidenceActive : Demand.ActiveRequirement
liabilityEvidenceActive = Demand.activeRequirement Consumer.legalConsumer Demand.legalLiabilityQuery
  Demand.resolvedLegalEvidenceCoordinate Demand.legalLiabilityNeedsResolvedEvidence "liability reuses resolved evidence"
liabilityAuthorityActive : Demand.ActiveRequirement
liabilityAuthorityActive = Demand.activeRequirement Consumer.legalConsumer Demand.legalLiabilityQuery
  Demand.legalSourceAuthorityCoordinate Demand.legalLiabilityNeedsLegalSourceAuthority "liability reuses authority"
liabilityJurisdictionActive : Demand.ActiveRequirement
liabilityJurisdictionActive = Demand.activeRequirement Consumer.legalConsumer Demand.legalLiabilityQuery
  Demand.resolvedLegalJurisdictionCoordinate Demand.legalLiabilityNeedsResolvedJurisdiction "liability reuses jurisdiction"

liabilityApplicabilityEvidence = Bridge.applicabilityReceiptPaysActiveCoordinate refl ownedApplicability
liabilityLegalRoleEvidence = Bridge.legalRoleReceiptPaysActiveCoordinate refl ownedLegalRole
liabilityResolvedEvidenceEvidence = Evidence.resolvedLegalEvidencePaysActiveCoordinate refl resolvedEvidence
liabilityAuthorityEvidence = Authority.legalSourceAuthorityPaysActiveCoordinate refl authorityReceipt
liabilityJurisdictionEvidence = Jurisdiction.legalJurisdictionPaysActiveCoordinate refl jurisdictionReceipt

liabilityApplicabilityPlan = Planner.planRequirement liabilityApplicabilityEvidence "reuse compiled applicability"
liabilityLegalRolePlan = Planner.planRequirement liabilityLegalRoleEvidence "reuse existing duty-bearer weld"
liabilityEvidencePlan = Planner.planRequirement liabilityResolvedEvidenceEvidence "reuse resolved evidence"
liabilityAuthorityPlan = Planner.planRequirement liabilityAuthorityEvidence "reuse legal authority"
liabilityJurisdictionPlan = Planner.planRequirement liabilityJurisdictionEvidence "reuse resolved jurisdiction"

liabilityViolationUnassessed : Planner.CoordinateEvidenceReceipt fixtureState liabilityViolationActive
liabilityViolationUnassessed = Planner.coordinateEvidenceReceipt Planner.currentUnassessed []
  "no WrongElementEvaluation/ViolationReceipt has yet been produced for this fixture"
  true refl true refl
liabilityViolationPlan = Planner.planRequirement liabilityViolationUnassessed
  "inspect wrong-element violation evidence"

liabilityApplicabilityReuses : Planner.action liabilityApplicabilityPlan ≡ Planner.reuseExisting
liabilityApplicabilityReuses = refl
liabilityLegalRoleReuses : Planner.action liabilityLegalRolePlan ≡ Planner.reuseExisting
liabilityLegalRoleReuses = refl
liabilityEvidenceReuses : Planner.action liabilityEvidencePlan ≡ Planner.reuseExisting
liabilityEvidenceReuses = refl
liabilityAuthorityReuses : Planner.action liabilityAuthorityPlan ≡ Planner.reuseExisting
liabilityAuthorityReuses = refl
liabilityJurisdictionReuses : Planner.action liabilityJurisdictionPlan ≡ Planner.reuseExisting
liabilityJurisdictionReuses = refl
liabilityViolationNeedsInspection : Planner.action liabilityViolationPlan ≡ Planner.inspectForEvidence
liabilityViolationNeedsInspection = refl

liabilityApplicabilityWork = Routing.routedWork Routing.noProducerInvocation refl Routing.reuseWithoutProducer "reuse applicability"
liabilityLegalRoleWork = Routing.routedWork Routing.noProducerInvocation refl Routing.reuseWithoutProducer "reuse legal role"
liabilityEvidenceWork = Routing.routedWork Routing.noProducerInvocation refl Routing.reuseWithoutProducer "reuse evidence"
liabilityAuthorityWork = Routing.routedWork Routing.noProducerInvocation refl Routing.reuseWithoutProducer "reuse authority"
liabilityJurisdictionWork = Routing.routedWork Routing.noProducerInvocation refl Routing.reuseWithoutProducer "reuse jurisdiction"
liabilityViolationWork = Routing.routedWork Routing.producerInvocationRequired refl
  (Routing.invokeProducer Routing.violationRoute)
  "inspect wrong elements; do not recompute applicability or role"

fixtureTruthStillUnresolved : Status.truthStatus fixtureProposition ≡ Status.truthUnresolved
fixtureTruthStillUnresolved = refl
fixtureOccurrenceStillAsserted : Status.occurrence fixtureEvent ≡ Status.assertedOccurrence
fixtureOccurrenceStillAsserted = refl

data FullyPaidFixtureProvesRealDogLaw : Set where
data FullyPaidPrerequisitesAdmitOccurrence : Set where
data FullyPaidPrerequisitesAdmitTruth : Set where
data UnrelatedParserCarrierPaidLegalPrerequisites : Set where
data LiabilityQueryRecomputesPaidApplicability : Set where

data LiabilityQueryRecomputesPaidLegalRole : Set where

fixtureDoesNotProveRealDogLaw : FullyPaidFixtureProvesRealDogLaw → ⊥
fixtureDoesNotProveRealDogLaw ()
fullyPaidPrerequisitesDoNotAdmitOccurrence : FullyPaidPrerequisitesAdmitOccurrence → ⊥
fullyPaidPrerequisitesDoNotAdmitOccurrence ()
fullyPaidPrerequisitesDoNotAdmitTruth : FullyPaidPrerequisitesAdmitTruth → ⊥
fullyPaidPrerequisitesDoNotAdmitTruth ()
unrelatedParserCarrierDoesNotPayLegalPrerequisites : UnrelatedParserCarrierPaidLegalPrerequisites → ⊥
unrelatedParserCarrierDoesNotPayLegalPrerequisites ()
liabilityDoesNotRecomputePaidApplicability : LiabilityQueryRecomputesPaidApplicability → ⊥
liabilityDoesNotRecomputePaidApplicability ()
liabilityDoesNotRecomputePaidLegalRole : LiabilityQueryRecomputesPaidLegalRole → ⊥
liabilityDoesNotRecomputePaidLegalRole ()

record FullyPaidApplicabilityFixtureBoundary : Set where
  constructor fully-paid-applicability-fixture-boundary
  field
    existingDogEventReused : Bool
    existingWrongTypeReused : Bool
    contextCompilerProducesExactProposition : Bool
    oneExactPropositionAcrossReceipts : Bool
    oneExactEventAcrossReceipts : Bool
    oneExactLegalStatusAcrossAuthorityJurisdictionMeet : Bool
    oneExactLegalSystemAcrossWrongSourceCase : Bool
    prerequisiteBundleInhabited : Bool
    allApplicabilityRequirementsReuseExisting : Bool
    applicabilityMeetCompiled : Bool
    applicabilityReceiptReusableDownstream : Bool
    existingLegalRoleWeldReusableDownstream : Bool
    liabilityReusesEvidenceAuthorityJurisdiction : Bool
    violationIsNextInspectionCut : Bool
    resultingApplicabilityStillCandidate : Bool
    truthStillUnresolved : Bool
    occurrenceStillAsserted : Bool
    provesRealDogLaw : Bool

canonicalFullyPaidApplicabilityFixtureBoundary : FullyPaidApplicabilityFixtureBoundary
canonicalFullyPaidApplicabilityFixtureBoundary =
  fully-paid-applicability-fixture-boundary
    true true true true true true true true true true true true true true true true true false
