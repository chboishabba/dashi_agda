module DASHI.Law.SensibLawOfflineResearchEngineRustReceiptsF93740fExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawProofSearchIterationReceiptABIExact as ABI

------------------------------------------------------------------------
-- EXACT LOCALLY VALIDATED RUST RECEIPT BUNDLE
--
-- These records pin deterministic runtime outputs emitted by slr at the exact
-- validated Rust head below.  They are runtime evidence only.  They do not
-- become legal authority, semantic truth, publication authority, or Agda proof.
------------------------------------------------------------------------

validatedRustRepository : String
validatedRustRepository = "chboishabba/slr"

validatedRustBranch : String
validatedRustBranch = "agent/offline-research-engine-v01"

validatedRustHead : String
validatedRustHead = "f93740fb28358836304383f45240f3621283bc03"

------------------------------------------------------------------------
-- Optional JSON string field, preserving JSON null distinctly from "".
------------------------------------------------------------------------

data OptionalString : Set where
  noString : OptionalString
  someString : String → OptionalString

------------------------------------------------------------------------
-- Existing single-gap offline loop receipt, regenerated/validated at f93740f.
------------------------------------------------------------------------

record OfflinePabaiLoopReceiptV01F93740f : Set where
  constructor offlinePabaiLoopReceiptV01F93740f
  field
    schemaVersion : String
    authority : String
    networkRequests : Nat
    consumerReference : String
    residualReference : String
    missingPropositionReference : String
    selectedMoveReference : String
    selectedSourceRevisionReference : String
    selectedStrategyReference : String
    artifactReference : String
    artifactDocumentReference : String
    artifactSourceRevisionReference : String
    artifactBytesDigestReference : String
    artifactNetworkRequests : Nat
    bridgeDocumentReference : String
    bridgeCanonicalTextDigestReference : String
    bridgeGraphReference : String
    correspondenceDocumentReference : String
    correspondenceGraphReference : String
    correspondencePropositionReference : String
    worldTruthClaimed : Bool
    legalHoldingClaimed : Bool
    assessmentGradeReference : String
    correspondenceStatusReference : String
    observedProofReduction : Nat
    dispositionReference : String
    changedCoordinateReferences : List String
    wakeReferences : List String
    nextMoveReference : String
    nextMoveStrategyReference : String
    deltaAuthorityReference : String
    iterationAuthorityReference : String
    rustHeadReference : String

open OfflinePabaiLoopReceiptV01F93740f public

canonicalOfflinePabaiLoopReceiptV01F93740f : OfflinePabaiLoopReceiptV01F93740f
canonicalOfflinePabaiLoopReceiptV01F93740f =
  offlinePabaiLoopReceiptV01F93740f
    "sensiblaw.offline-proof-search-loop-receipt.v0_1"
    "experimental_candidate_only"
    0
    "consumer:pabai-duty-route"
    "residual:positive-operational-act-comparator"
    "prop:cullen-positive-operational-act"
    "move:persisted-cullen-comparator"
    "source:cullen:rev:1"
    "PersistedAuthorityReceipt"
    "fixture:cullen"
    "doc:cullen"
    "source:cullen:rev:1"
    "sha256:cullen"
    0
    "doc:cullen"
    "sha256:cullen"
    "graph:cullen"
    "doc:cullen"
    "graph:cullen"
    "prop:cullen-positive-operational-act"
    false
    false
    "ComparatorOnly"
    "ReviewedSupported"
    2
    "Narrowed"
    ("prop:cullen-positive-operational-act" ∷ [])
    []
    "move:persisted-next-authority"
    "PersistedAuthorityReceipt"
    "experimental_candidate_only"
    "experimental_candidate_only"
    validatedRustHead

------------------------------------------------------------------------
-- Whole-frontier compounding receipt v0.2.
------------------------------------------------------------------------

record FrontierBaseIterationV01F93740f : Set where
  constructor frontierBaseIterationV01F93740f
  field
    schemaVersion : String
    runtimeHead : String
    consumerReference : String
    frontierReference : String
    proofGapReferences : List String
    candidateMoveReferences : List String
    paretoFrontierMoveReferences : List String
    selectedMoveReference : String
    selectedSourceRevisionReference : OptionalString
    executionCost : ABI.RuntimeCostVector
    artifactDigestReference : OptionalString
    pnfReceiptReference : OptionalString
    assessmentReference : OptionalString
    frontierDeltaReference : OptionalString
    wakeReferences : List String
    nextMoveReference : OptionalString
    authorityBoundaryReference : String
    inputDigestReference : String
    outputDigestReference : String

open FrontierBaseIterationV01F93740f public

record OfflineCompoundingIterationV02F93740f : Set where
  constructor offlineCompoundingIterationV02F93740f
  field
    schemaVersion : String
    baseIteration : FrontierBaseIterationV01F93740f
    priorFrontierReference : String
    nextFrontierReference : String
    changedResidualReferences : List String
    terminationReference : String
    worldSnapshotReference : String
    learnedQueryTerms : List String
    learnedAuthorityReferences : List String
    reasoningDeltaReferences : List String
    authorityBoundaryReference : String
    rustHeadReference : String

open OfflineCompoundingIterationV02F93740f public

canonicalCompoundingBaseIterationF93740f : FrontierBaseIterationV01F93740f
canonicalCompoundingBaseIterationF93740f =
  frontierBaseIterationV01F93740f
    "sl.proof_search_iteration.v0_1"
    "runtime:offline-compounding-v02"
    "consumer:pabai-duty-route"
    "frontier:pabai:v1"
    ("residual:positive-operational-act-comparator" ∷
     "residual:current-treatment" ∷ [])
    ("move:local-query:\"positive operational act\" AND (\"positive operational act\")" ∷
     "move:local-query:\"positive operational act\" AND (duty)" ∷
     "move:local-query:\"positive operational act\" AND (operational)" ∷ [])
    ("move:local-query:\"positive operational act\" AND (\"positive operational act\")" ∷ [])
    "move:local-query:\"positive operational act\" AND (\"positive operational act\")"
    noString
    (ABI.runtimeCostVector 0 0 0 0 0 1 0 1 0)
    (someString "sha256:cullen")
    (someString "pnf:cullen")
    (someString "assessment:cullen-comparator")
    (someString "delta:frontier:pabai:v2")
    []
    (someString "next:current-treatment")
    "experimental_candidate_only"
    "digest:input:v1"
    "digest:output:v2"

canonicalOfflineCompoundingIterationV02F93740f : OfflineCompoundingIterationV02F93740f
canonicalOfflineCompoundingIterationV02F93740f =
  offlineCompoundingIterationV02F93740f
    "sl.proof_search_frontier_iteration.v0_2"
    canonicalCompoundingBaseIterationF93740f
    "frontier:pabai:v1"
    "frontier:pabai:v2"
    ("residual:positive-operational-act-comparator" ∷ [])
    "Continue"
    "world:pabai:v1"
    ("positive operational act" ∷ [])
    ("authority:donoghue" ∷ [])
    ("reasoning:cullen:positive-operational-act" ∷ [])
    "experimental_candidate_only"
    validatedRustHead

------------------------------------------------------------------------
-- Local validation attestation associated with the exact Rust head.
------------------------------------------------------------------------

record LocalRustValidationAttestation : Set where
  constructor localRustValidationAttestation
  field
    rustHeadReference : String
    workspaceTestsPassed : Bool
    workspaceTestsPassedIsTrue : workspaceTestsPassed ≡ true
    strictClippyPassed : Bool
    strictClippyPassedIsTrue : strictClippyPassed ≡ true
    releaseBuildPassed : Bool
    releaseBuildPassedIsTrue : releaseBuildPassed ≡ true
    sourceContractsPassed : Bool
    sourceContractsPassedIsTrue : sourceContractsPassed ≡ true
    offlineFixturesPassed : Bool
    offlineFixturesPassedIsTrue : offlineFixturesPassed ≡ true
    bothReceiptsNetworkFree : Bool
    bothReceiptsNetworkFreeIsTrue : bothReceiptsNetworkFree ≡ true
    bothReceiptsCandidateOnly : Bool
    bothReceiptsCandidateOnlyIsTrue : bothReceiptsCandidateOnly ≡ true
    validationReference : String

open LocalRustValidationAttestation public

canonicalLocalRustValidationAttestationF93740f : LocalRustValidationAttestation
canonicalLocalRustValidationAttestationF93740f =
  localRustValidationAttestation
    validatedRustHead
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    "local-ci:f93740f:workspace-test+clippy+release+contracts+offline-fixtures"

------------------------------------------------------------------------
-- Exact receipt welds.
------------------------------------------------------------------------

v01SelectedAndArtifactSourceMatch :
  selectedSourceRevisionReference canonicalOfflinePabaiLoopReceiptV01F93740f ≡
  artifactSourceRevisionReference canonicalOfflinePabaiLoopReceiptV01F93740f
v01SelectedAndArtifactSourceMatch = refl

v01ArtifactAndBridgeDocumentMatch :
  artifactDocumentReference canonicalOfflinePabaiLoopReceiptV01F93740f ≡
  bridgeDocumentReference canonicalOfflinePabaiLoopReceiptV01F93740f
v01ArtifactAndBridgeDocumentMatch = refl

v01BridgeAndCorrespondenceGraphMatch :
  bridgeGraphReference canonicalOfflinePabaiLoopReceiptV01F93740f ≡
  correspondenceGraphReference canonicalOfflinePabaiLoopReceiptV01F93740f
v01BridgeAndCorrespondenceGraphMatch = refl

v01MissingAndCorrespondencePropositionMatch :
  missingPropositionReference canonicalOfflinePabaiLoopReceiptV01F93740f ≡
  correspondencePropositionReference canonicalOfflinePabaiLoopReceiptV01F93740f
v01MissingAndCorrespondencePropositionMatch = refl

v02PriorFrontierMatchesBase :
  priorFrontierReference canonicalOfflineCompoundingIterationV02F93740f ≡
  frontierReference canonicalCompoundingBaseIterationF93740f
v02PriorFrontierMatchesBase = refl

v02NetworkRequestsAreZero :
  ABI.networkRequests (executionCost canonicalCompoundingBaseIterationF93740f) ≡ 0
v02NetworkRequestsAreZero = refl

v02AuthorityBoundaryIsCandidateOnly :
  authorityBoundaryReference canonicalOfflineCompoundingIterationV02F93740f ≡
  "experimental_candidate_only"
v02AuthorityBoundaryIsCandidateOnly = refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data LocalRustValidationMeansAgdaKernelCertification : Set where
data CandidateSatisfiedResidualMeansLegalProofClosed : Set where
data LearnedQueryTermMeansDoctrine : Set where
data LearnedAuthorityNeighbourhoodMeansCurrentAuthority : Set where
\data RuntimeReceiptMeansPublicationAuthority : Set where

localRustValidationDoesNotMeanAgdaKernelCertification :
  LocalRustValidationMeansAgdaKernelCertification → ⊥
localRustValidationDoesNotMeanAgdaKernelCertification ()

candidateSatisfiedDoesNotMeanLegalProofClosed :
  CandidateSatisfiedResidualMeansLegalProofClosed → ⊥
candidateSatisfiedDoesNotMeanLegalProofClosed ()

learnedQueryTermDoesNotBecomeDoctrine : LearnedQueryTermMeansDoctrine → ⊥
learnedQueryTermDoesNotBecomeDoctrine ()

learnedAuthorityNeighbourhoodDoesNotBecomeCurrentAuthority :
  LearnedAuthorityNeighbourhoodMeansCurrentAuthority → ⊥
learnedAuthorityNeighbourhoodDoesNotBecomeCurrentAuthority ()

runtimeReceiptDoesNotBecomePublicationAuthority :
  RuntimeReceiptMeansPublicationAuthority → ⊥
runtimeReceiptDoesNotBecomePublicationAuthority ()

record RustReceiptBundleBoundary : Set where
  constructor rustReceiptBundleBoundary
  field
    exactRustHeadPinned : Bool
    exactRustHeadPinnedIsTrue : exactRustHeadPinned ≡ true
    singleGapReceiptPinned : Bool
    singleGapReceiptPinnedIsTrue : singleGapReceiptPinned ≡ true
    wholeFrontierReceiptPinned : Bool
    wholeFrontierReceiptPinnedIsTrue : wholeFrontierReceiptPinned ≡ true
    networkFreeExecutionPinned : Bool
    networkFreeExecutionPinnedIsTrue : networkFreeExecutionPinned ≡ true
    candidateOnlyAuthorityPinned : Bool
    candidateOnlyAuthorityPinnedIsTrue : candidateOnlyAuthorityPinned ≡ true
    learnedSearchCoordinatesRetained : Bool
    learnedSearchCoordinatesRetainedIsTrue : learnedSearchCoordinatesRetained ≡ true
    runtimeValidationEqualsAgdaProof : Bool
    runtimeValidationEqualsAgdaProofIsFalse : runtimeValidationEqualsAgdaProof ≡ false

canonicalRustReceiptBundleBoundary : RustReceiptBundleBoundary
canonicalRustReceiptBundleBoundary =
  rustReceiptBundleBoundary
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
