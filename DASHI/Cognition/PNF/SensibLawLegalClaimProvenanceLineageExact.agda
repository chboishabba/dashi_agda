module DASHI.Cognition.PNF.SensibLawLegalClaimProvenanceLineageExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra
import DASHI.Cognition.PNF.SensibLawSourceRealisedLegalRuleExact as SourceRule

------------------------------------------------------------------------
-- LEGAL CLAIM PROVENANCE LINEAGE
--
-- Repository attribution policy treats provenance as part of the claim
-- boundary.  The legal execution spine therefore keeps distinct:
--
--   external source claim / datum
--   secondary interpretation
--   DASHI formal reconstruction
--   DASHI cross-source inference
--   new DASHI theorem / synthetic extension
--   promotion / external adjudication
--
-- The existing PropositionSourceReceipt remains the canonical source carrier.
-- This owner only adds the stronger lineage stage; it does not replace source,
-- authority, semantic admission, applicability, proof, or adjudication owners.
------------------------------------------------------------------------

data LegalClaimProvenanceStage : Set where
  externalSourceClaim : LegalClaimProvenanceStage
  secondarySourceInterpretation : LegalClaimProvenanceStage
  repositoryReconstruction : LegalClaimProvenanceStage
  crossSourceInference : LegalClaimProvenanceStage
  repositoryTheoremExtension : LegalClaimProvenanceStage
  promotionOrExternalAdjudication : LegalClaimProvenanceStage

data LegalClaimLineage
    (p : Algebra.LegalProposition) :
    LegalClaimProvenanceStage → Set₁ where

  sourceClaimLineage :
    SourceRule.PropositionSourceReceipt p →
    LegalClaimLineage p externalSourceClaim

  secondaryInterpretationLineage :
    SourceRule.PropositionSourceReceipt p →
    String →
    LegalClaimLineage p secondarySourceInterpretation

  reconstructionLineage :
    SourceRule.PropositionSourceReceipt p →
    String →
    LegalClaimLineage p repositoryReconstruction

  crossSourceInferenceLineage :
    List Source.AttributedSource →
    String →
    LegalClaimLineage p crossSourceInference

  repositoryTheoremLineage :
    String →
    String →
    LegalClaimLineage p repositoryTheoremExtension

  promotionLineage :
    String →
    String →
    LegalClaimLineage p promotionOrExternalAdjudication

ClaimLineageReceipt : Algebra.LegalProposition → Set₁
ClaimLineageReceipt p =
  Σ LegalClaimProvenanceStage λ stage → LegalClaimLineage p stage

------------------------------------------------------------------------
-- Compatibility adapter from the pre-existing three-way legal source layer.
------------------------------------------------------------------------

lineageFromPropositionSourceReceipt :
  ∀ {p} →
  (receipt : SourceRule.PropositionSourceReceipt p) →
  ClaimLineageReceipt p
lineageFromPropositionSourceReceipt receipt
  with SourceRule.attributionLayer receipt
... | SourceRule.primarySourceLayer =
  externalSourceClaim , sourceClaimLineage receipt
... | SourceRule.secondaryInterpretationLayer =
  secondarySourceInterpretation ,
  secondaryInterpretationLineage receipt
    "legacy secondary-interpretation attribution layer retained"
... | SourceRule.repositoryReconstructionLayer =
  repositoryReconstruction ,
  reconstructionLineage receipt
    "legacy repository-reconstruction attribution layer retained"

stageOf : ∀ {p} → ClaimLineageReceipt p → LegalClaimProvenanceStage
stageOf = proj₁

------------------------------------------------------------------------
-- Firewalls: attribution lineage describes provenance.  It is not itself any
-- downstream legal or epistemic promotion permission.
------------------------------------------------------------------------

data AttributionCreatesTruth : Set where
data AttributionCreatesLegalAuthority : Set where
data AttributionCreatesApplicability : Set where
data AttributionCreatesRatio : Set where
data AttributionCreatesAdjudicatedFact : Set where
data ReconstructionMayBeAttributedBackToSourceAuthor : Set where
data CrossSourceInferenceMayPretendToBeSingleSourceClaim : Set where
data RepositoryTheoremMayPretendToBeExternalAdjudication : Set where

attributionDoesNotCreateTruth : AttributionCreatesTruth → ⊥
attributionDoesNotCreateTruth ()

attributionDoesNotCreateLegalAuthority : AttributionCreatesLegalAuthority → ⊥
attributionDoesNotCreateLegalAuthority ()

attributionDoesNotCreateApplicability : AttributionCreatesApplicability → ⊥
attributionDoesNotCreateApplicability ()

attributionDoesNotCreateRatio : AttributionCreatesRatio → ⊥
attributionDoesNotCreateRatio ()

attributionDoesNotCreateAdjudicatedFact : AttributionCreatesAdjudicatedFact → ⊥
attributionDoesNotCreateAdjudicatedFact ()

reconstructionCannotBeAttributedBackToSourceByPermission :
  ReconstructionMayBeAttributedBackToSourceAuthor → ⊥
reconstructionCannotBeAttributedBackToSourceByPermission ()

crossSourceInferenceCannotPretendToBeSingleSourceClaim :
  CrossSourceInferenceMayPretendToBeSingleSourceClaim → ⊥
crossSourceInferenceCannotPretendToBeSingleSourceClaim ()

repositoryTheoremDoesNotBecomeExternalAdjudication :
  RepositoryTheoremMayPretendToBeExternalAdjudication → ⊥
repositoryTheoremDoesNotBecomeExternalAdjudication ()

record LegalClaimProvenanceLineageBoundary : Set where
  constructor legal-claim-provenance-lineage-boundary
  field
    externalClaimSeparatedFromReconstruction : Bool
    reconstructionSeparatedFromCrossSourceInference : Bool
    crossSourceInferenceSeparatedFromRepositoryTheorem : Bool
    repositoryTheoremSeparatedFromPromotion : Bool
    legacySourceReceiptRetained : Bool
    provenanceCreatesTruth : Bool
    provenanceCreatesAuthority : Bool
    provenanceCreatesApplicability : Bool

canonicalLegalClaimProvenanceLineageBoundary :
  LegalClaimProvenanceLineageBoundary
canonicalLegalClaimProvenanceLineageBoundary =
  legal-claim-provenance-lineage-boundary
    true true true true true false false false
