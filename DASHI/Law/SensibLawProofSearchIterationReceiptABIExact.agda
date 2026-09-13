module DASHI.Law.SensibLawProofSearchIterationReceiptABIExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- DETERMINISTIC RUNTIME ITERATION RECEIPT ABI
--
-- Rust may emit canonical JSON for bounded runtime executions. Agda pins the
-- schema and exact fields as runtime evidence, but the receipt is never itself
-- promoted into a formal theorem or legal authority.
------------------------------------------------------------------------

record RuntimeCostVector : Set where
  constructor runtimeCostVector
  field
    networkRequests : Nat
    minimumPacingSeconds : Nat
    citationDepth : Nat
    maximumNewDocuments : Nat
    cacheMisses : Nat
    localBytesCost : Nat
    parserPNFCost : Nat
    semanticAssessmentCost : Nat
    operatorReviewCost : Nat

open RuntimeCostVector public

record ProofSearchIterationReceipt : Set₁ where
  constructor proofSearchIterationReceipt
  field
    schemaVersion : String
    runtimeHead : String
    consumerReference : String
    priorFrontierReference : String
    proofGapReferences : List String
    candidateMoveReferences : List String
    paretoFrontierMoveReferences : List String
    selectedMoveReference : String
    selectedSourceRevisionReference : String
    executionCost : RuntimeCostVector
    localArtifactDigestReference : String
    pnfReceiptReference : String
    assessmentReference : String
    frontierDeltaReference : String
    wakeReferences : List String
    nextMoveReference : String
    authorityBoundaryReference : String
    deterministicInputDigestReference : String
    deterministicOutputDigestReference : String
    receiptReference : String

open ProofSearchIterationReceipt public

record DeterministicReplayReceipt
    (left right : ProofSearchIterationReceipt) : Set₁ where
  constructor deterministicReplayReceipt
  field
    sameInputDigestReceipt : Set
    sameRuntimeHeadReceipt : Set
    samePolicyReceipt : Set
    sameOutputDigestReceipt : Set
    replayReference : String

open DeterministicReplayReceipt public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data RuntimeReceiptMeansFormalProof : Set where
data RuntimeReceiptMeansLegalAuthority : Set where
data SameSchemaMeansSameSemantics : Set where
data SameInputsPermitDifferentCanonicalReceipt : Set where

runtimeReceiptDoesNotMeanFormalProof : RuntimeReceiptMeansFormalProof → ⊥
runtimeReceiptDoesNotMeanFormalProof ()

runtimeReceiptDoesNotMeanLegalAuthority : RuntimeReceiptMeansLegalAuthority → ⊥
runtimeReceiptDoesNotMeanLegalAuthority ()

sameSchemaDoesNotMeanSameSemantics : SameSchemaMeansSameSemantics → ⊥
sameSchemaDoesNotMeanSameSemantics ()

canonicalReplayMustNotVary : SameInputsPermitDifferentCanonicalReceipt → ⊥
canonicalReplayMustNotVary ()

record IterationReceiptABIBoundary : Set where
  constructor iterationReceiptABIBoundary
  field
    exactRuntimeHeadRetained : Bool
    exactRuntimeHeadRetainedIsTrue : exactRuntimeHeadRetained ≡ true
    costVectorRetained : Bool
    costVectorRetainedIsTrue : costVectorRetained ≡ true
    frontierAndWakeRetained : Bool
    frontierAndWakeRetainedIsTrue : frontierAndWakeRetained ≡ true
    sameInputCanonicalReplayRequired : Bool
    sameInputCanonicalReplayRequiredIsTrue : sameInputCanonicalReplayRequired ≡ true
    runtimeReceiptEqualsFormalProof : Bool
    runtimeReceiptEqualsFormalProofIsFalse : runtimeReceiptEqualsFormalProof ≡ false

canonicalIterationReceiptABIBoundary : IterationReceiptABIBoundary
canonicalIterationReceiptABIBoundary =
  iterationReceiptABIBoundary true refl true refl true refl true refl false refl
