module DASHI.ComputerScience.RSA260BidiSeedByteCrossProverWeldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260BidiCoefficientByteCrossProverWeldExact as Coeff

------------------------------------------------------------------------
-- SEED-BYTE CROSS-PROVER WELD FRONTIER
--
-- Runtime V is now serialized canonically as one byte per matrix row, bit c
-- equal to block column c.  Lean derives the same 924-byte carrier structurally
-- from its formal seed generator.  This records convergence of representation,
-- not a kernel-certified same-object theorem.
------------------------------------------------------------------------

coefficientBoundary : Coeff.CoefficientByteCrossProverWeldBoundary
coefficientBoundary = Coeff.canonicalCoefficientByteCrossProverWeldBoundary

record SeedByteSourceReceipt : Set where
  constructor seed-byte-source-receipt
  field
    runtimeRepository : String
    runtimeBranch : String
    runtimeSourceCommit : String
    runtimeProducerPath : String
    runtimeRegressionPath : String
    runtimeByteCount : Nat
    runtimeSeedRowBytesSHA256 : String
    runtimeFirst16Hex : String
    runtimeLast16Hex : String

    leanRepository : String
    leanBranch : String
    leanSeedPath : String
    leanSeedBytesRegressionPath : String
    leanSeedBytesPath : String
    leanSeedBytesRedCommit : String
    leanSeedBytesSourceCommit : String
    leanSeedBytesRootCommit : String
open SeedByteSourceReceipt public

currentSeedByteSourceReceipt : SeedByteSourceReceipt
currentSeedByteSourceReceipt =
  seed-byte-source-receipt
    "chboishabba/dashiRTX"
    "agent/triadic-u8-runtime-oracle"
    "f1ef6130b9435589a3b7469dcda5ef0fb1f7d3c1"
    "rsa260_bidi_mksol_action_binding.py"
    "test_rsa260_bidi_seed_block_bytes.py"
    924
    "3cd881999d687ed98b37811f85a776fd3d11b03a381c898aab6f78b97e1701fe"
    "722cc23d374bf8d63ddf79b1b751abd8"
    "828ca4751131b2ff6c16b6b56c89b425"
    "chboishabba/dashi_lean4"
    "agent/rsa-consumer-kernel-bypass"
    "Synthesis/LinearConsumerSyntheticBidiSeed.lean"
    "Synthesis/LinearConsumerSyntheticBidiSeedBytesRegression.lean"
    "Synthesis/LinearConsumerSyntheticBidiSeedBytes.lean"
    "125a7560cd6dab3e0476af9c8ccfcb8eb40811eb"
    "dcd40a5d8cd4766686cf3239aed535efb3e6007c"
    "41a12c338768fbfc16964194c69f26e29dc5796c"

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data SeedByteSourcesCreateKernelEquality : Set where
data SeedFixtureCreatesProductionVIdentity : Set where

seedByteSourcesDoNotCreateKernelEquality : SeedByteSourcesCreateKernelEquality -> ⊥
seedByteSourcesDoNotCreateKernelEquality ()

seedFixtureDoesNotCreateProductionVIdentity : SeedFixtureCreatesProductionVIdentity -> ⊥
seedFixtureDoesNotCreateProductionVIdentity ()

record SeedByteCrossProverWeldBoundary : Set where
  constructor seed-byte-cross-prover-weld-boundary
  field
    runtimeSeedBytesExplicitlyRetained : Bool
    runtimeSeedByteCountIs924 : Bool
    runtimeSeedBytesHashRetained : Bool
    runtimeSeedByteRegressionWritten : Bool

    leanSeedGeneratorSourceWritten : Bool
    leanSeedByteSerializerDerivedStructurally : Bool
    leanSeedByteRegressionWritten : Bool
    commonRowByteConventionRecorded : Bool

    runtimeSeedBytesComparedToLeanBytes : Bool
    leanKernelReceiptObserved : Bool
    runtimeSeedBoundToLeanSeed : Bool
    runtimeActionBoundToLeanBaselineAction : Bool
    runtimeTwoVKernelBoundToFormalJointKernel : Bool

    productionVBlocksSameObjectPaid : Bool
    productionCADOMksolSemanticsPaid : Bool
    nextResidual : String
open SeedByteCrossProverWeldBoundary public

canonicalSeedByteCrossProverWeldBoundary : SeedByteCrossProverWeldBoundary
canonicalSeedByteCrossProverWeldBoundary =
  seed-byte-cross-prover-weld-boundary
    true true true true
    true true true true
    false false false false false
    false false
    "execute a finite source-pinned comparison of the runtime 924 seed row bytes against the Lean structural serializer and obtain a Lean kernel receipt.  After the synthetic V weld, compare the concrete Lean baseline action against the runtime action byte carrier. Production CADO V identity remains separate."
