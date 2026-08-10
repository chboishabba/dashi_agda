module DASHI.Cognition.PNF.DocumentScopedIdentityEvidenceExecution where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; _≤_)

------------------------------------------------------------------------
-- Migration 081 execution contract.
--
-- Identity evidence is still judged by the proof-relevant epistemic layer, but
-- execution is document-scoped before any minimum-span/window reduction occurs.
-- The document anchor is computed once and evidence lanes are fibres over that
-- shared carrier.  No constructor permits corpus-global anchor evaluation.
------------------------------------------------------------------------

data Scope : Set where
  selectedDocument corpusGlobal : Scope

data AnchorEvaluation : Scope → Set where
  documentScopedAnchor : AnchorEvaluation selectedDocument

corpusGlobalAnchorForbidden : AnchorEvaluation corpusGlobal → ⊥
corpusGlobalAnchorForbidden ()

record DocumentCarrier : Set where
  constructor documentCarrier
  field
    tokenCount : ℕ
    regionCount : ℕ
    entityCount : ℕ

open DocumentCarrier public

record DocumentAnchorCarrier (carrier : DocumentCarrier) : Set where
  constructor documentAnchorCarrier
  field
    evaluation : AnchorEvaluation selectedDocument
    anchoredTokenCount : ℕ
    anchoredWithinTokens : anchoredTokenCount ≤ tokenCount carrier

open DocumentAnchorCarrier public

data EvidenceLane : Set where
  appositionLane properNameLane aliasLane : EvidenceLane

-- All parser-evidence lanes consume the same document anchor carrier.  This is
-- the formal counterpart of SQL MATERIALIZED doc_anchor in migration 081.
record EvidenceFibre
  (carrier : DocumentCarrier)
  (anchor : DocumentAnchorCarrier carrier)
  (lane : EvidenceLane) : Set where
  constructor evidenceFibre

open EvidenceFibre public

record SharedAnchorExecution (carrier : DocumentCarrier) : Set where
  constructor sharedAnchorExecution
  field
    anchor : DocumentAnchorCarrier carrier
    apposition : EvidenceFibre carrier anchor appositionLane
    properName : EvidenceFibre carrier anchor properNameLane
    alias : EvidenceFibre carrier anchor aliasLane

open SharedAnchorExecution public

-- Work is bounded by the selected document carrier rather than the corpus
-- carrier.  The theorem intentionally states a structural bound, not a wall-time
-- claim: the runtime still needs empirical query-plan validation.
record DocumentScopedWorkBound
  (selected corpus : DocumentCarrier) : Set where
  constructor documentScopedWorkBound
  field
    selectedTokensWithinCorpus : tokenCount selected ≤ tokenCount corpus
    selectedRegionsWithinCorpus : regionCount selected ≤ regionCount corpus
    selectedEntitiesWithinCorpus : entityCount selected ≤ entityCount corpus

open DocumentScopedWorkBound public

record IdentityEvidenceExecutionBoundary : Set where
  constructor identityEvidenceExecutionBoundary
  field
    corpusAnchorDenied : AnchorEvaluation corpusGlobal → ⊥

open IdentityEvidenceExecutionBoundary public

canonicalIdentityEvidenceExecutionBoundary : IdentityEvidenceExecutionBoundary
canonicalIdentityEvidenceExecutionBoundary =
  identityEvidenceExecutionBoundary corpusGlobalAnchorForbidden
