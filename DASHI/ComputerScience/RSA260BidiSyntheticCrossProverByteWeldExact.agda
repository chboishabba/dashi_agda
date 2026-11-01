module DASHI.ComputerScience.RSA260BidiSyntheticCrossProverByteWeldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260BidiRuntimeKrylovActionBindingExact as Runtime
import DASHI.ComputerScience.RSA260BidiLeanKrylovFamilyActionBindingExact as Lean

------------------------------------------------------------------------
-- POST-MERGE SYNTHETIC CROSS-PROVER BYTE WELD CANDIDATE
--
-- The merged #938 tranche already owns a hash-bound executed dashiRTX baseline
-- and the generic Lean Krylov action source.  The Lean branch has since gained
-- independent finite runtime fixtures and exact source theorems for:
--
--   * recovered coefficient bytes: 136 bytes = 17 layers x 8 rows;
--   * deterministic seed bytes:     924 bytes = one byte per 8-bit block row;
--   * final baseline action bytes:   924 bytes = one byte per 8-bit block row.
--
-- The coefficient fixture was checked externally against the exact runtime
-- 136-byte carrier and is byte-for-byte equal.  Seed/action runtime fixtures
-- were extracted from the same executed baseline source and encoded independently
-- on the Lean side.  This file records SOURCE status only: no Lean kernel receipt
-- has yet been observed for those equality theorems.
--
-- dashiRTX has concurrently advanced to a producer that also contains the
-- extensional incidence formula and an exhaustive runtime-A vs Lean-style-A
-- comparison, but that exact latest producer head has not been re-executed here.
------------------------------------------------------------------------

runtimeReceipt : Runtime.RuntimeKrylovActionReceipt
runtimeReceipt = Runtime.currentRuntimeKrylovActionReceipt

leanBoundary : Lean.LeanKrylovFamilyActionBindingBoundary
leanBoundary = Lean.canonicalLeanKrylovFamilyActionBindingBoundary

record SyntheticCrossProverByteWeldSourceReceipt : Set where
  constructor synthetic-cross-prover-byte-weld-source-receipt
  field
    leanRepository : String
    leanBranch : String
    coefficientEqualityRegressionCommit : String
    coefficientEqualitySourceCommit : String
    coefficientEqualityRootCommit : String
    runtimeByteEqualityRegressionCommit : String
    runtimeByteEqualitySourceCommit : String
    runtimeByteEqualityRootCommit : String

    runtimeRepository : String
    runtimeBranch : String
    executedRuntimeCommit : String
    executedRuntimeSourceBlob : String
    executedRuntimeOutputSHA256 : String
    latestRuntimeSourceHead : String
    latestRuntimeProducerBlob : String
open SyntheticCrossProverByteWeldSourceReceipt public

currentSyntheticCrossProverByteWeldSourceReceipt :
  SyntheticCrossProverByteWeldSourceReceipt
currentSyntheticCrossProverByteWeldSourceReceipt =
  synthetic-cross-prover-byte-weld-source-receipt
    "chboishabba/dashi_lean4"
    "agent/rsa-consumer-kernel-bypass"
    "8c040e7c5f1ad3f7b939d87be84116247155de71"
    "416df718f40f43da9663902c7c32468b841e2aa0"
    "fd323a9dd3ba707c059335f84b59d199a7837c5d"
    "2ae3ec422229d1536b4214921a76f36d2d34b301"
    "c8925405f3ec7134765bc1fd069e294f4ccfd792"
    "18097d9a52bbe1d671f05277bd20d7c4077328bc"
    "chboishabba/dashiRTX"
    "agent/triadic-u8-runtime-oracle"
    "ea67564df1628ac1752424ce78ad08907db06458"
    "fee6116ad8c16b8c66a058c2d637453e9548a6df"
    "3473d9dcd3f327f3045aa46eecdb6e2fa104b2962013224eaf3f02f5bd6fdbf6"
    "3b7fdd6fce355373caf3a47ae47c5b58c9ff27d7"
    "a89420c23543a284d8ee7a253ddaee1209a771ac"

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data SourceEqualityCreatesKernelReceipt : Set where
data SyntheticWeldCreatesCADOSemantics : Set where
data SyntheticWeldCreatesProductionRSA260 : Set where

sourceEqualityDoesNotCreateKernelReceipt :
  SourceEqualityCreatesKernelReceipt -> ⊥
sourceEqualityDoesNotCreateKernelReceipt ()

syntheticWeldDoesNotCreateCADOSemantics :
  SyntheticWeldCreatesCADOSemantics -> ⊥
syntheticWeldDoesNotCreateCADOSemantics ()

syntheticWeldDoesNotCreateProductionRSA260 :
  SyntheticWeldCreatesProductionRSA260 -> ⊥
syntheticWeldDoesNotCreateProductionRSA260 ()

record SyntheticCrossProverByteWeldBoundary : Set where
  constructor synthetic-cross-prover-byte-weld-boundary
  field
    executedBaselineSourceHashBound : Bool
    executedBaselineOutputHashBound : Bool
    runtimeCoefficientBytesObserved : Bool
    runtimeSeedBytesObserved : Bool
    runtimeActionBytesObserved : Bool

    leanCoefficientByteEqualitySourceWritten : Bool
    leanSeedByteEqualitySourceWritten : Bool
    leanActionByteEqualitySourceWritten : Bool
    leanPreparedOperatorSourceWritten : Bool
    leanSyntheticIncidenceSourceWritten : Bool

    leanKernelReceiptObserved : Bool
    latestRuntimeProducerReexecuted : Bool
    latestRuntimeIncidenceEqualityObserved : Bool

    runtimeCoefficientBoundToLeanCoefficientFamily : Bool
    runtimeSeedBoundToLeanSeedBlock : Bool
    runtimeActionBoundToLeanBaselineAction : Bool
    runtimeIncidenceBoundToLeanIncidence : Bool
    runtimeApplyBBoundToLeanPreparedOperator : Bool
    runtimeTwoVKernelBoundToFormalJointKernel : Bool

    exactCADOMksolSemanticsPaid : Bool
    productionSameObjectCarrierPaid : Bool
    nextResidual : String
open SyntheticCrossProverByteWeldBoundary public

canonicalSyntheticCrossProverByteWeldBoundary :
  SyntheticCrossProverByteWeldBoundary
canonicalSyntheticCrossProverByteWeldBoundary =
  synthetic-cross-prover-byte-weld-boundary
    true true true true true
    true true true true true
    false false false
    false false false false false false
    false false
    "kernel-check the Lean exact coefficient/seed/action byte-equality theorems and re-execute the latest dashiRTX producer that exhaustively compares build_A with the Lean-style incidence formula. Only then promote the synthetic runtime coefficient, seed, incidence, prepared-operator and action identities; after that bind the checked two-V runtime zero-kernel matrix to Lean jointKernel. CADO/production identity remains independent."
