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
-- SourceRule.PropositionSourceReceipt remains the canonical source carrier.
-- Its LegalAttributionLayer describes the SOURCE ATTACHMENT.  It does not by
-- itself decide the provenance stage of the repository proposition object.
-- A DASHI formalisation may therefore carry a primary-source receipt while its
-- claim-provenance stage remains repositoryReconstruction.
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

stageOf : ∀ {p} → ClaimLineageReceipt p → LegalClaimProvenanceStage
stageOf = proj₁

------------------------------------------------------------------------
-- Explicit constructors for the common legal-source cases.
------------------------------------------------------------------------

externalClaimFromSourceReceipt :
  ∀ {p} →
  SourceRule.PropositionSourceReceipt p →
  ClaimLineageReceipt p
externalClaimFromSourceReceipt receipt =
  externalSourceClaim , sourceClaimLineage receipt

reconstructionFromSourceReceipt :
  ∀ {p} →
  SourceRule.PropositionSourceReceipt p →
  String →
  ClaimLineageReceipt p
reconstructionFromSourceReceipt receipt reference =
  repositoryReconstruction , reconstructionLineage receipt reference

secondaryInterpretationFromSourceReceipt :
  ∀ {p} →
  SourceRule.PropositionSourceReceipt p →
  String →
  ClaimLineageReceipt p
secondaryInterpretationFromSourceReceipt receipt reference =
  secondarySourceInterpretation , secondaryInterpretationLineage receipt reference

------------------------------------------------------------------------
-- Compatibility adapter from the pre-existing three-way legal SOURCE layer.
-- This is a default rendering of that attachment layer only.  Callers that
-- know a repository proposition is a DASHI reconstruction of a primary source
-- should use reconstructionFromSourceReceipt instead of this adapter.
------------------------------------------------------------------------

legacyAttributionLayerDefaultLineage :
  ∀ {p} →
  (receipt : SourceRule.PropositionSourceReceipt p) →
  ClaimLineageReceipt p
legacyAttributionLayerDefaultLineage receipt
  with SourceRule.attributionLayer receipt
... | SourceRule.primarySourceLayer =
  externalClaimFromSourceReceipt receipt
... | SourceRule.secondaryInterpretationLayer =
  secondaryInterpretationFromSourceReceipt receipt
    "legacy secondary-interpretation attribution layer retained"
... | SourceRule.repositoryReconstructionLayer =
  reconstructionFromSourceReceipt receipt
    "legacy repository-reconstruction attribution layer retained"

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
data PrimarySourceLayerForcesExternalClaimStage : Set where

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

primarySourceAttachmentDoesNotForceExternalClaimStage :
  PrimarySourceLayerForcesExternalClaimStage → ⊥
primarySourceAttachmentDoesNotForceExternalClaimStage ()

record LegalClaimProvenanceLineageBoundary : Set where
  constructor legal-claim-provenance-lineage-boundary
  field
    externalClaimSeparatedFromReconstruction : Bool
    reconstructionSeparatedFromCrossSourceInference : Bool
    crossSourceInferenceSeparatedFromRepositoryTheorem : Bool
    repositoryTheoremSeparatedFromPromotion : Bool
    sourceAttachmentLayerSeparatedFromClaimProvenanceStage : Bool
    legacySourceReceiptRetained : Bool
    provenanceCreatesTruth : Bool
    provenanceCreatesAuthority : Bool
    provenanceCreatesApplicability : Bool

canonicalLegalClaimProvenanceLineageBoundary :
  LegalClaimProvenanceLineageBoundary
canonicalLegalClaimProvenanceLineageBoundary =
  legal-claim-provenance-lineage-boundary
    true true true true true true false false false
