module DASHI.ComputerScience.RSA260BidiRuntimeKrylovActionBindingExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260BidiLeanKrylovFamilyActionBindingExact as Lean

------------------------------------------------------------------------
-- HASH-BOUND SYNTHETIC RUNTIME KRYLOV/ACTION BINDING
--
-- The canonical executable producer now lives in dashiRTX, not in a detached
-- notebook path.  Its committed source is byte-identical (Git blob identity)
-- to the locally executed source that produced the receipt below.
--
-- The runtime pays:
--   K_0 = V;
--   K_{i+1} = apply_B K_i for every checked layer;
--   stored sum_i K_i F_i = streaming recurrence evaluation;
-- plus shape-bound digests for A, permutation, V, F, K and the action.
--
-- It still does NOT identify runtime apply_B with Lean M, runtime V/F with the
-- Lean carriers, or this synthetic evaluator with exact CADO mksol semantics.
------------------------------------------------------------------------

leanBoundary : Lean.LeanKrylovFamilyActionBindingBoundary
leanBoundary = Lean.canonicalLeanKrylovFamilyActionBindingBoundary

record RuntimeKrylovActionReceipt : Set where
  constructor runtime-krylov-action-receipt
  field
    repository : String
    branch : String
    donorPath : String
    regressionPath : String
    producerPath : String
    redCommit : String
    firstProducerCommit : String
    schemaAlignmentCommit : String
    executedSourceGitBlob : String
    executedSourceSHA256 : String
    outputSHA256 : String

    degree : Nat
    coefficientLayerCount : Nat
    coefficientRows : Nat
    coefficientCols : Nat
    seedRows : Nat
    seedCols : Nat
    actionRows : Nat
    actionCols : Nat

    matrixASHA256 : String
    identityPermutationSHA256 : String
    seedVSHA256 : String
    coefficientFamilySHA256 : String
    krylovFamilySHA256 : String
    actionSHA256 : String

    sourceBlobMatchesExecutedSource : Bool
    krylovRecurrenceAllEqual : Bool
    storedActionEqualsStreamingAction : Bool
    operatorLinearitySpotcheck : Bool
    exactLocalRuntimeExecuted : Bool
open RuntimeKrylovActionReceipt public

currentRuntimeKrylovActionReceipt : RuntimeKrylovActionReceipt
currentRuntimeKrylovActionReceipt =
  runtime-krylov-action-receipt
    "chboishabba/dashiRTX"
    "agent/triadic-u8-runtime-oracle"
    "rsa260_bidi_candidate_robustness.py"
    "test_rsa260_bidi_mksol_action_binding.py"
    "rsa260_bidi_mksol_action_binding.py"
    "dbcb85d959fcc79441e1f921c2e9d3cf2b605426"
    "d1b4530205b2cbb8fa5de5efbb96a6543e161586"
    "ea67564df1628ac1752424ce78ad08907db06458"
    "fee6116ad8c16b8c66a058c2d637453e9548a6df"
    "b79868ffb0468acbfe5f84c42ab86d512d47a364e192e79e8e8a596ebf1647c7"
    "3473d9dcd3f327f3045aa46eecdb6e2fa104b2962013224eaf3f02f5bd6fdbf6"
    17 17 8 8 924 8 924 8
    "d25f6dc6148fef994b803bf763835e6ceda13cd1fdb7ed62faa5f34e64a2b09d"
    "fd6d77fd6b3d8de1f7488177bae85ff304a8725aa2063289d036a6e3c5cd5113"
    "97c477b4a7aa0078f6eadd5f93759cbbccc34e7aa4c841d0418c4a55caf29ffc"
    "251fe2d2b2fdb0ba2cededcc5ee2d65331784b981d02857da01edd4f6c377b6b"
    "1e112febfb1d046a8e885c0388c180f3faf484d92d115ff18dccf53879fde06b"
    "1a78a9b446945536f5bc067747c7e2da7d2dbd12dfa775bec19f8a595e55ae88"
    true true true true true

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data RuntimeReceiptCreatesLeanIdentity : Set where
data RuntimeReceiptCreatesCADOSemantics : Set where
data RuntimeReceiptCreatesProductionRSA260 : Set where

runtimeReceiptDoesNotCreateLeanIdentity : RuntimeReceiptCreatesLeanIdentity -> ⊥
runtimeReceiptDoesNotCreateLeanIdentity ()

runtimeReceiptDoesNotCreateCADOSemantics : RuntimeReceiptCreatesCADOSemantics -> ⊥
runtimeReceiptDoesNotCreateCADOSemantics ()

runtimeReceiptDoesNotCreateProductionRSA260 : RuntimeReceiptCreatesProductionRSA260 -> ⊥
runtimeReceiptDoesNotCreateProductionRSA260 ()

record RuntimeKrylovActionBindingBoundary : Set where
  constructor runtime-krylov-action-binding-boundary
  field
    canonicalRuntimeProducerCommitted : Bool
    committedSourceEqualsExecutedSource : Bool
    rectangularCarrierShapesObserved : Bool
    runtimeKrylovRecurrencePaid : Bool
    runtimeStoredStreamingActionEqualityPaid : Bool
    runtimeObjectDigestsRetained : Bool

    runtimeApplyBBoundToLeanM : Bool
    runtimeSeedVBoundToLeanV : Bool
    runtimeRecoveredFBoundToLeanF : Bool
    runtimeActionBoundToLeanKrylovAction : Bool
    runtimeTwoVKernelBoundToFormalJointKernel : Bool

    exactCADOMksolSemanticsPaid : Bool
    productionSameObjectCarrierPaid : Bool
    nextResidual : String
open RuntimeKrylovActionBindingBoundary public

canonicalRuntimeKrylovActionBindingBoundary : RuntimeKrylovActionBindingBoundary
canonicalRuntimeKrylovActionBindingBoundary =
  runtime-krylov-action-binding-boundary
    true true true true true true
    false false false false false
    false false
    "construct the cross-prover same-object weld identifying this hash-bound runtime apply_B/V/F/K action with the Lean rectangular Krylov family action; only then transport the checked two-V runtime kernel matrix into Lean jointKernel. Exact CADO/production bindings remain separate."
