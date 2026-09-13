module DASHI.Cognition.PNF.SensibLawProvenanceSemanticStatusOrthogonalityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra
import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status
import DASHI.Cognition.PNF.SensibLawLegalClaimProvenanceLineageExact as Provenance

------------------------------------------------------------------------
-- PROVENANCE x SEMANTIC STATUS ORTHOGONALITY
--
-- Provenance answers "where/how did this repository claim arise?".
-- PropositionStatusProduct answers "what semantic/epistemic status is currently
-- admitted for this exact proposition?". LegalStatusProduct separately carries
-- authority/applicability/violation/liability coordinates.
--
-- None of these axes is derived from another by construction.
------------------------------------------------------------------------

record ProvenanceSemanticStatusReceipt
    (p : Algebra.LegalProposition) : Set₁ where
  constructor provenance-semantic-status-receipt
  field
    lineage : Provenance.ClaimLineageReceipt p
    propositionStatus : Status.PropositionStatusProduct
    legalStatus : Status.LegalStatusProduct
    sameProposition :
      Ontology.stableId (Status.propositionReference propositionStatus)
      ≡ Algebra.propositionId p
    statusReference : String

open ProvenanceSemanticStatusReceipt public

------------------------------------------------------------------------
-- The exact same proposition may be source-attributed while still unresolved,
-- alleged, represented-only, rejected, found as fact, held, etc.  The status
-- owner must pay those distinctions independently.
------------------------------------------------------------------------

data ExternalSourceClaimImpliesTruthAdmitted : Set where
data PrimarySourceImpliesFoundAsFact : Set where
data CaseLawSourceImpliesHeldByCourt : Set where
data RepositoryReconstructionImpliesInferenceOnlyStatus : Set where
data CrossSourceInferenceImpliesCandidateTrue : Set where
data PromotionStageMaySkipPromotionAuthority : Set where
data PropositionStatusCreatesLegalAuthority : Set where
data LegalAuthorityCreatesTruthStatus : Set where

externalSourceDoesNotAdmitTruth : ExternalSourceClaimImpliesTruthAdmitted → ⊥
externalSourceDoesNotAdmitTruth ()

primarySourceDoesNotCreateFindingOfFact : PrimarySourceImpliesFoundAsFact → ⊥
primarySourceDoesNotCreateFindingOfFact ()

caseLawSourceDoesNotCreateHoldingStatus : CaseLawSourceImpliesHeldByCourt → ⊥
caseLawSourceDoesNotCreateHoldingStatus ()

reconstructionDoesNotForceInferenceOnlyStatus :
  RepositoryReconstructionImpliesInferenceOnlyStatus → ⊥
reconstructionDoesNotForceInferenceOnlyStatus ()

crossSourceInferenceDoesNotAdmitTruth : CrossSourceInferenceImpliesCandidateTrue → ⊥
crossSourceInferenceDoesNotAdmitTruth ()

promotionStageDoesNotBypassPromotionAuthority :
  PromotionStageMaySkipPromotionAuthority → ⊥
promotionStageDoesNotBypassPromotionAuthority ()

propositionStatusDoesNotCreateLegalAuthority :
  PropositionStatusCreatesLegalAuthority → ⊥
propositionStatusDoesNotCreateLegalAuthority ()

legalAuthorityDoesNotCreateTruthStatus : LegalAuthorityCreatesTruthStatus → ⊥
legalAuthorityDoesNotCreateTruthStatus ()

record ProvenanceSemanticStatusOrthogonalityBoundary : Set where
  constructor provenance-semantic-status-orthogonality-boundary
  field
    exactPropositionWeldRequired : Bool
    provenanceAndPropositionStatusIndependent : Bool
    propositionStatusAndLegalStatusIndependent : Bool
    sourceAttributionCreatesTruth : Bool
    caseSourceCreatesHolding : Bool
    legalAuthorityCreatesTruth : Bool

canonicalProvenanceSemanticStatusOrthogonalityBoundary :
  ProvenanceSemanticStatusOrthogonalityBoundary
canonicalProvenanceSemanticStatusOrthogonalityBoundary =
  provenance-semantic-status-orthogonality-boundary
    true true true false false false
