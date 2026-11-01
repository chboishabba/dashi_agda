module DASHI.Cognition.PNF.SensibLawResolvedLegalEvidenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status
import DASHI.Cognition.PNF.SensibLawConsumerQuerySemanticCoordinateReopeningExact as Demand
import DASHI.Cognition.PNF.SensibLawActiveRequirementExecutionPlannerExact as Planner
import DASHI.Cognition.PNF.SensibLawLiveProducerCoordinateEvidenceBridgeExact as Bridge

------------------------------------------------------------------------
-- RESOLVED LEGAL-USE EVIDENCE
--
-- Evidence discovery/provenance candidates are weaker than legal-use evidence.
-- This receipt welds an actual EvidenceItem/EventEvidenceLink to the exact event
-- and proposition living in the current semantic state. Parser evidence alone
-- is deliberately excluded from the legal-use evidence-kind witness family.
------------------------------------------------------------------------

data LegalUseEvidenceKind : Status.EvidenceKind → Set where
  sourceEvidenceLegalUse : LegalUseEvidenceKind Status.sourceEvidence
  testimonialEvidenceLegalUse : LegalUseEvidenceKind Status.testimonialEvidence
  documentaryEvidenceLegalUse : LegalUseEvidenceKind Status.documentaryEvidence
  provenanceEvidenceLegalUse : LegalUseEvidenceKind Status.provenanceEvidence
  externalEvidenceLegalUse : LegalUseEvidenceKind Status.externalEvidence

record ResolvedLegalEvidenceReceiptInState
    (state : Status.SemanticCommitmentState) : Set where
  constructor resolvedLegalEvidenceReceiptInState
  field
    evidenceItem : Ontology.EvidenceItem
    eventLink : Ontology.EventEvidenceLink
    eventStatus : Status.EventStatusProduct
    propositionStatus : Status.PropositionStatusProduct
    eventMembership : Bridge._∈_ eventStatus (Status.events state)
    propositionMembership : Bridge._∈_ propositionStatus (Status.propositions state)
    linkTargetsExactEvent :
      Ontology.EventEvidenceLink.linkedEvent eventLink
      ≡ Ontology.stableId (Status.eventReference eventStatus)
    linkTargetsExactEvidence :
      Ontology.EventEvidenceLink.linkedEvidence eventLink
      ≡ Ontology.EvidenceItem.evidenceId evidenceItem
    evidenceKindResolved : LegalUseEvidenceKind (Status.evidenceKind propositionStatus)
    evidencePolarityResolved : Bool
    evidencePolarityResolvedIsTrue : evidencePolarityResolved ≡ true
    provenanceReferences : List String
    evidenceReference : String

open ResolvedLegalEvidenceReceiptInState public

resolvedLegalEvidencePaysActiveCoordinate :
  ∀ {state active} →
  Demand.coordinate active ≡ Demand.resolvedLegalEvidenceCoordinate →
  ResolvedLegalEvidenceReceiptInState state →
  Planner.CoordinateEvidenceReceipt state active
resolvedLegalEvidencePaysActiveCoordinate same receipt =
  Planner.coordinateEvidenceReceipt
    Planner.currentResolved
    (provenanceReferences receipt)
    (evidenceReference receipt)
    true refl true refl

------------------------------------------------------------------------
-- Weak evidence currencies do not promote automatically.
------------------------------------------------------------------------

record LegalEvidenceCandidate : Set where
  constructor legalEvidenceCandidate
  field
    evidenceItem : Ontology.EvidenceItem
    candidateReferences : List String
    exactEventChecked : Bool
    exactPropositionChecked : Bool
    legalUseKindChecked : Bool
    provenanceChecked : Bool

open LegalEvidenceCandidate public

data ParserEvidencePaysResolvedLegalEvidence : Set where
data EvidenceItemExistencePaysResolvedLegalEvidence : Set where
data EventLinkAlonePaysPropositionEvidence : Set where
data RepeatedEvidenceCountsAsIndependentLegalEvidence : Set where
data ResolvedLegalEvidenceAdmitsTruth : Set where

parserEvidenceDoesNotPayResolvedLegalEvidence :
  ParserEvidencePaysResolvedLegalEvidence → ⊥
parserEvidenceDoesNotPayResolvedLegalEvidence ()

evidenceItemExistenceDoesNotPayResolvedLegalEvidence :
  EvidenceItemExistencePaysResolvedLegalEvidence → ⊥
evidenceItemExistenceDoesNotPayResolvedLegalEvidence ()

eventLinkAloneDoesNotPayPropositionEvidence :
  EventLinkAlonePaysPropositionEvidence → ⊥
eventLinkAloneDoesNotPayPropositionEvidence ()

repetitionDoesNotCreateIndependentLegalEvidence :
  RepeatedEvidenceCountsAsIndependentLegalEvidence → ⊥
repetitionDoesNotCreateIndependentLegalEvidence ()

resolvedLegalEvidenceDoesNotAdmitTruth :
  ResolvedLegalEvidenceAdmitsTruth → ⊥
resolvedLegalEvidenceDoesNotAdmitTruth ()

record ResolvedLegalEvidenceBoundary : Set where
  constructor resolved-legal-evidence-boundary
  field
    parserEvidenceAloneCanPay : Bool
    exactEventMembershipRequired : Bool
    exactPropositionMembershipRequired : Bool
    exactEvidenceLinkRequired : Bool
    legalUseEvidenceKindRequired : Bool
    provenanceRetained : Bool
    resolvedEvidenceAdmitsTruth : Bool

canonicalResolvedLegalEvidenceBoundary : ResolvedLegalEvidenceBoundary
canonicalResolvedLegalEvidenceBoundary =
  resolved-legal-evidence-boundary false true true true true true false
