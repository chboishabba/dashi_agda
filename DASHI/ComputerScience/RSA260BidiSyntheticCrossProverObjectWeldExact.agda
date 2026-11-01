module DASHI.ComputerScience.RSA260BidiSyntheticCrossProverObjectWeldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260BidiRuntimeKrylovActionBindingExact as Runtime
import DASHI.ComputerScience.RSA260BidiLeanKrylovFamilyActionBindingExact as Lean

------------------------------------------------------------------------
-- SYNTHETIC CROSS-PROVER OBJECT-WELD FRONTIER
--
-- After merged #938, the Lean bypass no longer contains only generic matrix
-- algebra.  On `agent/rsa-consumer-kernel-bypass` it now has concrete formal
-- mirrors of the deterministic baseline synthetic objects:
--
--   * incidence A : 924 x 512 over GF(2);
--   * identity-permutation prepared operator M_A(Y)=A(A^T Y);
--   * deterministic seed block V : 924 x 8;
--   * recovered degree-17 coefficient family F_i : 17 x 8 x 8;
--   * generic Krylov action F |-> sum_i (M^i V) F_i.
--
-- The dashiRTX producer independently owns a hash-bound executable copy of the
-- baseline runtime objects.  This module records the convergence of the two
-- source surfaces while deliberately leaving their same-object equality unpaid.
------------------------------------------------------------------------

runtimeBoundary : Runtime.RuntimeKrylovActionBindingBoundary
runtimeBoundary = Runtime.canonicalRuntimeKrylovActionBindingBoundary

leanBoundary : Lean.LeanKrylovFamilyActionBindingBoundary
leanBoundary = Lean.canonicalLeanKrylovFamilyActionBindingBoundary

record SyntheticCrossProverObjectWeldSourceReceipt : Set where
  constructor synthetic-cross-prover-object-weld-source-receipt
  field
    leanRepository : String
    leanBranch : String
    leanSourceHead : String
    preparedOperatorPath : String
    incidencePath : String
    seedPath : String
    coefficientPath : String
    krylovActionPath : String
    coefficientRegressionCommit : String
    coefficientSourceCommit : String
    coefficientRootCommit : String
    runtimeRepository : String
    runtimeBranch : String
    runtimeSourceCommit : String
    runtimeSourceBlob : String
    runtimeCoefficientFamilySHA256 : String
open SyntheticCrossProverObjectWeldSourceReceipt public

currentSyntheticCrossProverObjectWeldSourceReceipt :
  SyntheticCrossProverObjectWeldSourceReceipt
currentSyntheticCrossProverObjectWeldSourceReceipt =
  synthetic-cross-prover-object-weld-source-receipt
    "chboishabba/dashi_lean4"
    "agent/rsa-consumer-kernel-bypass"
    "53b98594afef09f31a4a1fc13d9e2f4674c1c714"
    "Synthesis/LinearConsumerPreparedOperator.lean"
    "Synthesis/LinearConsumerSyntheticBidiIncidence.lean"
    "Synthesis/LinearConsumerSyntheticBidiSeed.lean"
    "Synthesis/LinearConsumerSyntheticBidiCoefficients.lean"
    "Synthesis/LinearConsumerKrylovFamilyAction.lean"
    "540b4dd040ac0189f5da5be1572a2a4d2dec09df"
    "d009fc3ac4a0a98925c999c579cc69b7bc51fba6"
    "53b98594afef09f31a4a1fc13d9e2f4674c1c714"
    "chboishabba/dashiRTX"
    "agent/triadic-u8-runtime-oracle"
    "ea67564df1628ac1752424ce78ad08907db06458"
    "fee6116ad8c16b8c66a058c2d637453e9548a6df"
    "251fe2d2b2fdb0ba2cededcc5ee2d65331784b981d02857da01edd4f6c377b6b"

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data ParallelSourceMirrorsCreateSameObjectEquality : Set where
data FiniteFixtureCreatesKernelReceipt : Set where
data SyntheticWeldCreatesProductionCADO : Set where

parallelMirrorsDoNotCreateSameObjectEquality :
  ParallelSourceMirrorsCreateSameObjectEquality -> ⊥
parallelMirrorsDoNotCreateSameObjectEquality ()

finiteFixtureDoesNotCreateKernelReceipt :
  FiniteFixtureCreatesKernelReceipt -> ⊥
finiteFixtureDoesNotCreateKernelReceipt ()

syntheticWeldDoesNotCreateProductionCADO :
  SyntheticWeldCreatesProductionCADO -> ⊥
syntheticWeldDoesNotCreateProductionCADO ()

record SyntheticCrossProverObjectWeldBoundary : Set where
  constructor synthetic-cross-prover-object-weld-boundary
  field
    runtimeHashBoundProducerPaid : Bool
    leanPreparedOperatorSourceWritten : Bool
    leanSyntheticIncidenceSourceWritten : Bool
    leanSyntheticSeedSourceWritten : Bool
    leanSyntheticCoefficientFixtureWritten : Bool
    leanKrylovActionSourceWritten : Bool
    runtimeCoefficientDigestRetained : Bool

    leanKernelReceiptObserved : Bool
    runtimeIncidenceBoundToLeanIncidence : Bool
    runtimePreparedOperatorBoundToLeanPreparedOperator : Bool
    runtimeSeedBoundToLeanSeed : Bool
    runtimeRecoveredCoefficientsBoundToLeanFixture : Bool
    runtimeActionBoundToLeanKrylovAction : Bool
    twoVRuntimeKernelBoundToFormalJointKernel : Bool

    exactCADOMksolSemanticsPaid : Bool
    productionPreparedOperatorSameObjectPaid : Bool
    productionVBlocksSameObjectPaid : Bool
    productionGeneratorSameObjectPaid : Bool

    nextResidual : String
open SyntheticCrossProverObjectWeldBoundary public

canonicalSyntheticCrossProverObjectWeldBoundary :
  SyntheticCrossProverObjectWeldBoundary
canonicalSyntheticCrossProverObjectWeldBoundary =
  synthetic-cross-prover-object-weld-boundary
    true
    true
    true
    true
    true
    true
    true
    false
    false
    false
    false
    false
    false
    false
    false
    false
    false
    false
    "kernel-check the Lean donor/fixtures, then prove or execute finite cross-language equality for the runtime incidence A, identity-permutation prepared operator, seed block V, and recovered 17-layer F fixture. Once those object identities are paid, the runtime action equality should descend through the already-owned Krylov action theorem; only then bind the two-V runtime kernel matrix to Lean jointKernel. Production CADO identities remain a separate lane."
