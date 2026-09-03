module DASHI.Cognition.PNF.SensibLawLegalSourceAuthorityEvidenceExact where

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
import DASHI.Cognition.PNF.SensibLawLegalSemanticAdmissionFrontierExact as Admission

------------------------------------------------------------------------
-- LEGAL-SOURCE AUTHORITY EVIDENCE
--
-- This is deliberately distinct from semantic admission authority.  A
-- SemanticAdmissionReceipt may authorize resolution/admission of a semantic
-- candidate; it does not establish that a statute/case/treaty is authoritative
-- law for a legal applicability query.
------------------------------------------------------------------------

data SourceValidityStatus : Set where
  validityCurrent
  validityExpired
  validityRepealed
  validitySuperseded
  validityUnresolved
  : SourceValidityStatus

data CurrentValidity : SourceValidityStatus → Set where
  currentValidity : CurrentValidity validityCurrent

record LegalSourceAuthorityReceiptInState
    (state : Status.SemanticCommitmentState) : Set where
  constructor legalSourceAuthorityReceiptInState
  field
    source : Ontology.LegalSource
    system : Ontology.LegalSystem
    sourceSystemMatches :
      Ontology.LegalSource.sourceSystem source ≡ Ontology.LegalSystem.systemId system
    legalStatus : Status.LegalStatusProduct
    legalStatusMembership : legalStatus Bridge.∈ Status.legalStatuses state
    authorityIsLegal : Status.authorityKind legalStatus ≡ Status.legalAuthority
    validity : SourceValidityStatus
    validityIsCurrent : CurrentValidity validity
    sourceEvidenceReferences : List String
    validityEvidenceReferences : List String
    authorityEvidenceReferences : List String
    authorityReference : String

open LegalSourceAuthorityReceiptInState public

legalSourceAuthorityPaysActiveCoordinate :
  ∀ {state active} →
  Demand.coordinate active ≡ Demand.legalSourceAuthorityCoordinate →
  LegalSourceAuthorityReceiptInState state →
  Planner.CoordinateEvidenceReceipt state active
legalSourceAuthorityPaysActiveCoordinate same receipt =
  Planner.coordinateEvidenceReceipt
    Planner.currentResolved
    ( authorityEvidenceReferences receipt )
    ( authorityReference receipt )
    true refl true refl

------------------------------------------------------------------------
-- Candidate source recognition is weaker than authority closure.
------------------------------------------------------------------------

record LegalSourceCandidate : Set where
  constructor legalSourceCandidate
  field
    source : Ontology.LegalSource
    candidateEvidenceReferences : List String
    sourceSystemChecked : Bool
    validityChecked : Bool
    authorityChecked : Bool

open LegalSourceCandidate public

data CandidateSourceIsAuthoritative : Set where
data SameLegalSystemAutomaticallyMeansAuthority : Set where
data CurrentValidityAutomaticallyMeansApplicability : Set where
data SemanticAdmissionAuthorityIsLegalSourceAuthority : Set where
data DocumentRoleSuppliesLegalSourceAuthority : Set where

candidateSourceDoesNotCloseAuthority : CandidateSourceIsAuthoritative → ⊥
candidateSourceDoesNotCloseAuthority ()

sameSystemDoesNotAutomaticallyCloseAuthority :
  SameLegalSystemAutomaticallyMeansAuthority → ⊥
sameSystemDoesNotAutomaticallyCloseAuthority ()

currentValidityDoesNotAutomaticallyEstablishApplicability :
  CurrentValidityAutomaticallyMeansApplicability → ⊥
currentValidityDoesNotAutomaticallyEstablishApplicability ()

semanticAdmissionDoesNotBecomeLegalSourceAuthority :
  SemanticAdmissionAuthorityIsLegalSourceAuthority → ⊥
semanticAdmissionDoesNotBecomeLegalSourceAuthority ()

documentRoleDoesNotSupplyLegalSourceAuthority :
  DocumentRoleSuppliesLegalSourceAuthority → ⊥
documentRoleDoesNotSupplyLegalSourceAuthority ()

semanticAdmissionReceiptCannotPayLegalSourceAuthority :
  ∀ {candidate} →
  Admission.SemanticAdmissionReceipt candidate →
  SemanticAdmissionAuthorityIsLegalSourceAuthority → ⊥
semanticAdmissionReceiptCannotPayLegalSourceAuthority receipt =
  semanticAdmissionDoesNotBecomeLegalSourceAuthority

record LegalSourceAuthorityBoundary : Set where
  constructor legal-source-authority-boundary
  field
    legalSourceRecordAloneIsAuthority : Bool
    sourceSystemIdentityRequired : Bool
    currentValidityRequired : Bool
    legalAuthorityStatusRequired : Bool
    semanticAdmissionAuthorityCanSubstitute : Bool
    legalSourceAuthorityAloneEstablishesApplicability : Bool

canonicalLegalSourceAuthorityBoundary : LegalSourceAuthorityBoundary
canonicalLegalSourceAuthorityBoundary =
  legal-source-authority-boundary false true true true false false
