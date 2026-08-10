module DASHI.Cognition.PNF.DocumentScopedIdentityEvidenceExecution where

open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; _≤_)

------------------------------------------------------------------------
-- Migrations 081 and 083 execution contract.
--
-- Identity evidence is judged by the proof-relevant epistemic layer, while
-- execution is document-scoped before any minimum-span reduction occurs. Exact
-- object-token support is the primary observation bridge; span containment is a
-- fallback only when exact support is absent. Evidence lanes are fibres over one
-- shared document anchor carrier. No constructor permits corpus-global anchor
-- evaluation or fallback in the presence of exact support.
------------------------------------------------------------------------

data Scope : Set where
  selectedDocument corpusGlobal : Scope

data AnchorEvaluation : Scope → Set where
  documentScopedAnchor : AnchorEvaluation selectedDocument

corpusGlobalAnchorForbidden : AnchorEvaluation corpusGlobal → ⊥
corpusGlobalAnchorForbidden ()

data ExactSupportAvailability : Set where
  exactSupportPresent exactSupportAbsent : ExactSupportAvailability

data AnchorRoute : ExactSupportAvailability → Set where
  exactTokenSupportRoute : AnchorRoute exactSupportPresent
  spanFallbackRoute : AnchorRoute exactSupportAbsent

fallbackWithExactSupportForbidden : AnchorRoute exactSupportPresent → Set
fallbackWithExactSupportForbidden exactTokenSupportRoute = Set

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

-- All parser-evidence lanes consume the same document anchor carrier. This is
-- the formal counterpart of SQL MATERIALIZED doc_anchor.
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
-- carrier. The theorem intentionally states a structural bound, not wall time.
record DocumentScopedWorkBound
  (selected corpus : DocumentCarrier) : Set where
  constructor documentScopedWorkBound
  field
    selectedTokensWithinCorpus : tokenCount selected ≤ tokenCount corpus
    selectedRegionsWithinCorpus : regionCount selected ≤ regionCount corpus
    selectedEntitiesWithinCorpus : entityCount selected ≤ entityCount corpus

open DocumentScopedWorkBound public

-- Semantic refresh transactions are document scoped. This mirrors the runtime
-- runner releasing locks and committing/retracting proof state per document.
data SemanticRefreshTransactionScope : Set where
  documentRefreshTransaction : SemanticRefreshTransactionScope

record IdentityEvidenceExecutionBoundary : Set where
  constructor identityEvidenceExecutionBoundary
  field
    corpusAnchorDenied : AnchorEvaluation corpusGlobal → ⊥
    refreshTransaction : SemanticRefreshTransactionScope

open IdentityEvidenceExecutionBoundary public

canonicalIdentityEvidenceExecutionBoundary : IdentityEvidenceExecutionBoundary
canonicalIdentityEvidenceExecutionBoundary =
  identityEvidenceExecutionBoundary
    corpusGlobalAnchorForbidden
    documentRefreshTransaction
