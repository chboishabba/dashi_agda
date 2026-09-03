module DASHI.Cognition.PNF.SensibLawLegalJurisdictionEvidenceExact where

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
-- RESOLVED LEGAL JURISDICTION
--
-- A location mention or document provenance may propose a jurisdiction
-- candidate.  Applicability requires a legal-system-relative jurisdiction
-- receipt.  Geographic jurisdiction is deliberately excluded from the resolved
-- legal-jurisdiction witness family below.
------------------------------------------------------------------------

data ResolvedLegalJurisdiction : Status.JurisdictionKind → Set where
  legalSystemResolved : ResolvedLegalJurisdiction Status.legalSystemJurisdiction
  courtResolved : ResolvedLegalJurisdiction Status.courtJurisdiction
  personalResolved : ResolvedLegalJurisdiction Status.personalJurisdiction
  subjectMatterResolved : ResolvedLegalJurisdiction Status.subjectMatterJurisdiction

record LegalJurisdictionReceiptInState
    (state : Status.SemanticCommitmentState) : Set where
  constructor legalJurisdictionReceiptInState
  field
    caseFrame : Ontology.CaseFrame
    system : Ontology.LegalSystem
    caseSystemMatches :
      Ontology.CaseFrame.legalSystemId caseFrame
      ≡ Ontology.LegalSystem.systemId system
    legalStatus : Status.LegalStatusProduct
    legalStatusMembership : Bridge._∈_ legalStatus (Status.legalStatuses state)
    jurisdictionResolved :
      ResolvedLegalJurisdiction (Status.jurisdictionKind legalStatus)
    jurisdictionEvidenceReferences : List String
    systemEvidenceReferences : List String
    jurisdictionReference : String

open LegalJurisdictionReceiptInState public

legalJurisdictionPaysActiveCoordinate :
  ∀ {state active} →
  Demand.coordinate active ≡ Demand.resolvedLegalJurisdictionCoordinate →
  LegalJurisdictionReceiptInState state →
  Planner.CoordinateEvidenceReceipt state active
legalJurisdictionPaysActiveCoordinate same receipt =
  Planner.coordinateEvidenceReceipt
    Planner.currentResolved
    (jurisdictionEvidenceReferences receipt)
    (jurisdictionReference receipt)
    true refl true refl

------------------------------------------------------------------------
-- Candidate jurisdiction is weaker.
------------------------------------------------------------------------

record JurisdictionCandidate : Set where
  constructor jurisdictionCandidate
  field
    candidateKind : Status.JurisdictionKind
    evidenceReferences : List String
    legalSystemIdentityChecked : Bool
    legalStatusResolved : Bool

open JurisdictionCandidate public

data GeographicMentionIsResolvedLegalJurisdiction : Set where
data CaseFrameSystemAloneFixesJurisdictionKind : Set where
data LegalSystemRecordAloneEstablishesApplicability : Set where
data JurisdictionCandidatePaysResolvedLegalJurisdiction : Set where
\ ngeographicMentionDoesNotResolveLegalJurisdiction :
  GeographicMentionIsResolvedLegalJurisdiction → ⊥
geographicMentionDoesNotResolveLegalJurisdiction ()

caseSystemAloneDoesNotFixJurisdictionKind :
  CaseFrameSystemAloneFixesJurisdictionKind → ⊥
caseSystemAloneDoesNotFixJurisdictionKind ()

legalSystemRecordDoesNotEstablishApplicability :
  LegalSystemRecordAloneEstablishesApplicability → ⊥
legalSystemRecordDoesNotEstablishApplicability ()

jurisdictionCandidateDoesNotPayResolvedLegalJurisdiction :
  JurisdictionCandidatePaysResolvedLegalJurisdiction → ⊥
jurisdictionCandidateDoesNotPayResolvedLegalJurisdiction ()

record LegalJurisdictionBoundary : Set where
  constructor legal-jurisdiction-boundary
  field
    geographicMentionAloneResolvesLegalJurisdiction : Bool
    exactCaseSystemIdentityRequired : Bool
    resolvedLegalJurisdictionKindRequired : Bool
    jurisdictionCandidateCanSubstitute : Bool
    resolvedJurisdictionAloneEstablishesApplicability : Bool

canonicalLegalJurisdictionBoundary : LegalJurisdictionBoundary
canonicalLegalJurisdictionBoundary =
  legal-jurisdiction-boundary false true true false false
