module DASHI.Cognition.PNF.SensibLawFullyPaidApplicabilityFixtureExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Cognition.PNF.SensibLawSpacyCompositionOnlySemanticConstitutionExact as Constitution
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

------------------------------------------------------------------------
-- FULLY-PAID REGRESSION FIXTURE
--
-- This is a proof fixture, not a claim about real dog-walking law.  It reuses
-- the existing canonical dog Event/Perspective/WrongType/system interpretation
-- and adds the missing same-object legal-source/evidence/context/scope receipts
-- needed to exercise the complete applicability compiler.
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
    Document.neutralNarrative
    ("existing canonical dog-walk fixture" ∷ [])
    "fixture document-context resolver"
    false refl false refl

------------------------------------------------------------------------
-- Same proposition/event statuses.
------------------------------------------------------------------------

fixtureProposition : Status.PropositionStatusProduct
fixtureProposition =
  Status.propositionStatusProduct
    "dog-walked-positive"
    Status.assertedBySource
    Status.truthUnresolved
    Status.propositionSource
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

-- neutralNarrative changes the proposition-status to represented and attribution
-- to unresolved.  For this fully-paid applicability fixture we therefore retain
-- the exact asserted proposition directly as the contextual proposition owner;
-- the DocumentDiscourseFrame itself supplies context but does not rewrite it.
fixtureContextProposition : Status.PropositionStatusProduct
fixtureContextProposition = fixtureProposition

------------------------------------------------------------------------
-- One exact legal-status object pays both authority and jurisdiction.
------------------------------------------------------------------------

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
    Status.judicialStatusUnresolved
    Status.normativeRelationUnresolved

------------------------------------------------------------------------
-- State.  The source candidate is an existing parser-derived Constitution
-- carrier used only to satisfy the generic state container; none of the proof
-- obligations below may be discharged by that unrelated parser carrier.
------------------------------------------------------------------------

fixtureState : Status.SemanticCommitmentState
fixtureState =
  Status.semanticCommitmentState
    PdfPlanner.pdfConstitutionFibre
    []
    (fixtureEvent ∷ [])
    (fixtureProposition ∷ [])
    (fixtureLegalStatus ∷ [])
    true false

ownedProposition : Bridge.PropositionReceiptInState fixtureState
ownedProposition =
  Bridge.propositionReceiptInState
    fixturePropositionReceipt Bridge.here
    "fixture proposition exact state membership"

ownedOccurrence : Bridge.OccurrenceReceiptInState fixtureState
ownedOccurrence =
  Bridge.occurrenceReceiptInState
    fixtureOccurrenceReceipt Bridge.here
    "fixture event exact state membership"

ownedDocumentContext : Bridge.DocumentContextReceiptInState fixtureState
ownedDocumentContext =
  Bridge.documentContextReceiptInState
    fixtureDocumentFrame fixtureContextProposition Bridge.here
    "fixture case/document context over exact proposition"

------------------------------------------------------------------------
-- Evidence.
------------------------------------------------------------------------

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
  Ontology.attachEvidence
    Vertical.dogEvent fixtureEvidenceItem "supports asserted dog-walk proposition"

resolvedEvidence : Evidence.ResolvedLegalEvidenceReceiptInState fixtureState
resolvedEvidence =
  Evidence.resolvedLegalEvidenceReceiptInState
    fixtureEvidenceItem
    fixtureEvidenceLink
    fixtureEvent
    fixtureProposition
    Bridge.here
    Bridge.here
    refl
    refl
    Evidence.documentaryEvidenceLegalUse
    true refl
    ("provenance:fixture:dog-walk-document" ∷ [])
    "fixture resolved documentary evidence"

------------------------------------------------------------------------
-- Authority and jurisdiction over the same legal status/system.
------------------------------------------------------------------------

authorityReceipt : Authority.LegalSourceAuthorityReceiptInState fixtureState
authorityReceipt =
  Authority.legalSourceAuthorityReceiptInState
    fixtureSource
    fixtureSystem
    refl
    fixtureLegalStatus
    Bridge.here
    refl
    Authority.validityCurrent
    Authority.currentValidity
    ("Fixture Dog Duty Act s 1" ∷ [])
    ("fixture validity interval checked" ∷ [])
    ("fixture source recognized as legal authority" ∷ [])
    "fixture legal-source authority"

jurisdictionReceipt : Jurisdiction.LegalJurisdictionReceiptInState fixtureState
jurisdictionReceipt =
  Jurisdiction.legalJurisdictionReceiptInState
    fixtureCase
    fixtureSystem
    refl
    fixtureLegalStatus
    Bridge.here
    Jurisdiction.legalSystemResolved
    ("fixture case legal-system identity" ∷ [])
    ("fixture legal system record" ∷ [])
    "fixture resolved legal-system jurisdiction"

------------------------------------------------------------------------
-- Same-object resolved scope.
------------------------------------------------------------------------

fixtureScopeBody : Candidate.Formula
fixtureScopeBody =
  Candidate.atom "Walk"
    (Candidate.eventTerm "event:dog-walk" ∷
     Candidate.entityTerm "actor:X" ∷ [])

fixtureScopeReceipt : Scope.ScopeCompositionReceipt
fixtureScopeReceipt =
  Scope.scopeCompositionReceipt
    fixtureProposition
    fixtureEvent
    fixtureScopeBody
    []
    Status.modalityKindUnresolved
    Status.modalForceUnresolved
    Status.scopeResolved
    Status.scopeResolved
    Status.conditionUnresolved
    Status.scopeResolved
    Status.eventTime
    Status.scopeResolved
    "fixture joint scope resolution"
    false false

ownedScope : Bridge.ResolvedScopeReceiptInState fixtureState
ownedScope =
  Bridge.resolvedScopeReceiptInState
    fixtureScopeReceipt
    Bridge.here
    Bridge.here
    refl refl refl refl
    "fixture same-object resolved scope"

------------------------------------------------------------------------
-- Strong prerequisite bundle: every receipt is literally about the same
-- proposition/event/status/system.
------------------------------------------------------------------------

prerequisites : Meet.ApplicabilityPrerequisiteBundle fixtureState
prerequisites =
  Meet.applicabilityPrerequisiteBundle
    ownedProposition
    ownedOccurrence
    ownedDocumentContext
    resolvedEvidence
    authorityReceipt
    jurisdictionReceipt
    ownedScope
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    "fully-paid fixture same-object prerequisite bundle"

------------------------------------------------------------------------
-- Semantic legal input remains candidate-only because the event is asserted,
-- not admitted.  Paying legal prerequisites does not upgrade occurrence/truth.
------------------------------------------------------------------------

semanticInput : Legal.SemanticLegalInputGate Vertical.dogEvent
semanticInput =
  Legal.semanticLegalInputGate
    fixtureEvent
    fixtureProposition
    refl
    Status.applicabilityCandidate
    Legal.assertionCandidateUse

meetInput : Meet.ApplicabilityMeetInput fixtureState
meetInput =
  Meet.applicabilityMeetInput
    prerequisites
    Vertical.dogEvent
    LegalRoleLive.fixtureWrongType
    LegalRoleLive.fixtureInterpretation
    semanticInput
    fixtureLegalStatus
    Bridge.here
    refl
    refl
    refl
    refl
    refl
    "fully-paid same-object fixture typed meet"
    "fixture event time"
    "fixture exceptions checked"

compiledApplicability : Legal.WrongTypeApplicabilityReceipt
compiledApplicability = Meet.compileApplicabilityMeet meetInput

compiledApplicabilityIsStillCandidate :
  Legal.resultingApplicability compiledApplicability ≡ Status.applicabilityCandidate
compiledApplicabilityIsStillCandidate = refl

fixtureTruthStillUnresolved :
  Status.truthStatus fixtureProposition ≡ Status.truthUnresolved
fixtureTruthStillUnresolved = refl

fixtureOccurrenceStillAsserted :
  Status.occurrence fixtureEvent ≡ Status.assertedOccurrence
fixtureOccurrenceStillAsserted = refl

------------------------------------------------------------------------
-- Boundaries.
------------------------------------------------------------------------

data FullyPaidFixtureProvesRealDogLaw : Set where
data FullyPaidPrerequisitesAdmitOccurrence : Set where
data FullyPaidPrerequisitesAdmitTruth : Set where
data UnrelatedParserCarrierPaidLegalPrerequisites : Set where

fixtureDoesNotProveRealDogLaw : FullyPaidFixtureProvesRealDogLaw → ⊥
fixtureDoesNotProveRealDogLaw ()

fullyPaidPrerequisitesDoNotAdmitOccurrence : FullyPaidPrerequisitesAdmitOccurrence → ⊥
fullyPaidPrerequisitesDoNotAdmitOccurrence ()

fullyPaidPrerequisitesDoNotAdmitTruth : FullyPaidPrerequisitesAdmitTruth → ⊥
fullyPaidPrerequisitesDoNotAdmitTruth ()

unrelatedParserCarrierDoesNotPayLegalPrerequisites :
  UnrelatedParserCarrierPaidLegalPrerequisites → ⊥
unrelatedParserCarrierDoesNotPayLegalPrerequisites ()

record FullyPaidApplicabilityFixtureBoundary : Set where
  constructor fully-paid-applicability-fixture-boundary
  field
    existingDogEventReused : Bool
    existingWrongTypeReused : Bool
    oneExactPropositionAcrossReceipts : Bool
    oneExactEventAcrossReceipts : Bool
    oneExactLegalStatusAcrossAuthorityJurisdictionMeet : Bool
    oneExactLegalSystemAcrossWrongSourceCase : Bool
    prerequisiteBundleInhabited : Bool
    applicabilityMeetCompiled : Bool
    resultingApplicabilityStillCandidate : Bool
    truthStillUnresolved : Bool
    occurrenceStillAsserted : Bool
    provesRealDogLaw : Bool

canonicalFullyPaidApplicabilityFixtureBoundary :
  FullyPaidApplicabilityFixtureBoundary
canonicalFullyPaidApplicabilityFixtureBoundary =
  fully-paid-applicability-fixture-boundary
    true true true true true true true true true true true false
