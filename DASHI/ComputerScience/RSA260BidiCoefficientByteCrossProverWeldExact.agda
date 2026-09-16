module DASHI.ComputerScience.RSA260BidiCoefficientByteCrossProverWeldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260BidiSyntheticCrossProverObjectWeldExact as Objects

------------------------------------------------------------------------
-- COEFFICIENT-BYTE CROSS-PROVER WELD FRONTIER
--
-- dashiRTX now exposes the recovered baseline F family as exactly 136 row
-- bytes, with a pinned SHA-256.  dashi_lean4 independently exposes a canonical
-- 136-byte serializer for its 17 x 8 x 8 finite GF(2) coefficient fixture.
--
-- This puts both producers on one finite representation carrier.  Source
-- agreement and an intended common convention are not promoted into a Lean
-- kernel theorem or cross-prover same-object equality here.
------------------------------------------------------------------------

objectBoundary : Objects.SyntheticCrossProverObjectWeldBoundary
objectBoundary = Objects.canonicalSyntheticCrossProverObjectWeldBoundary

record CoefficientByteSourceReceipt : Set where
  constructor coefficient-byte-source-receipt
  field
    runtimeRepository : String
    runtimeBranch : String
    runtimeCommit : String
    runtimeProducerPath : String
    runtimeRegressionPath : String
    runtimeByteCount : Nat
    runtimeRowBytesSHA256 : String
    runtimeRowBytesHex : String

    leanRepository : String
    leanBranch : String
    leanHead : String
    leanCoefficientPath : String
    leanByteBridgeRegressionPath : String
    leanByteBridgePath : String
    leanByteBridgeRedCommit : String
    leanByteBridgeSourceCommit : String
    leanByteBridgeRootCommit : String
open CoefficientByteSourceReceipt public

currentCoefficientByteSourceReceipt : CoefficientByteSourceReceipt
currentCoefficientByteSourceReceipt =
  coefficient-byte-source-receipt
    "chboishabba/dashiRTX"
    "agent/triadic-u8-runtime-oracle"
    "7c869e2a44750292653b25833bcc2708df32edd6"
    "rsa260_bidi_mksol_action_binding.py"
    "test_rsa260_bidi_mksol_action_binding.py"
    136
    "2545d4185bffa89562aebf7405a1db81443a7d49f64aeb83dc564a940ce13e79"
    "000000000000000048480048484848488d5e681991b956ba9ecf127bd9c3402f149d07f109827ffc74c77c54eb2f0ff73e86c7e4655b2423764903ed69d18482a77a93909d8940e8aa606979f949c0233bf6207175d6e49ec94f905edb01a69a9a2b6a0ca90a1f6ee740e77e71033f36b1a922f45c7d6582ad213da4146ada00005300000000000000"
    "chboishabba/dashi_lean4"
    "agent/rsa-consumer-kernel-bypass"
    "1e3542098a6a644a6d0916d4286d33e8b92f366b"
    "Synthesis/LinearConsumerSyntheticBidiCoefficients.lean"
    "Synthesis/LinearConsumerSyntheticBidiCoefficientBytesRegression.lean"
    "Synthesis/LinearConsumerSyntheticBidiCoefficientBytes.lean"
    "5da10473cff3d6d2163293ced86b6dbeab8037a1"
    "332ad6201f19bd606289dd5da048892081ccf4ca"
    "1e3542098a6a644a6d0916d4286d33e8b92f366b"

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data SourceByteConventionCreatesKernelEquality : Set where
data ByteEqualityCreatesProductionGeneratorIdentity : Set where

data RuntimeHashCreatesLeanKernelReceipt : Set where

sourceByteConventionDoesNotCreateKernelEquality :
  SourceByteConventionCreatesKernelEquality -> ⊥
sourceByteConventionDoesNotCreateKernelEquality ()

byteEqualityDoesNotCreateProductionGeneratorIdentity :
  ByteEqualityCreatesProductionGeneratorIdentity -> ⊥
byteEqualityDoesNotCreateProductionGeneratorIdentity ()

runtimeHashDoesNotCreateLeanKernelReceipt : RuntimeHashCreatesLeanKernelReceipt -> ⊥
runtimeHashDoesNotCreateLeanKernelReceipt ()

record CoefficientByteCrossProverWeldBoundary : Set where
  constructor coefficient-byte-cross-prover-weld-boundary
  field
    runtimeCoefficientBytesExplicitlyRetained : Bool
    runtimeCoefficientByteCountIs136 : Bool
    runtimeCoefficientBytesHashRetained : Bool
    runtimeCoefficientByteRegressionWritten : Bool

    leanCoefficientFixtureSourceWritten : Bool
    leanCanonical136ByteSerializerSourceWritten : Bool
    leanByteRegressionWritten : Bool
    commonRowMajorConventionRecorded : Bool

    leanKernelReceiptObserved : Bool
    leanSerializerEvaluatedToRuntimeBytes : Bool
    runtimeCoefficientBytesBoundToLeanBytes : Bool
    runtimeRecoveredFBoundToLeanCoefficientFamily : Bool
    runtimeActionBoundToLeanBaselineAction : Bool
    runtimeTwoVKernelBoundToFormalJointKernel : Bool

    productionGeneratorSameObjectPaid : Bool
    productionCADOMksolSemanticsPaid : Bool
    nextResidual : String
open CoefficientByteCrossProverWeldBoundary public

canonicalCoefficientByteCrossProverWeldBoundary :
  CoefficientByteCrossProverWeldBoundary
canonicalCoefficientByteCrossProverWeldBoundary =
  coefficient-byte-cross-prover-weld-boundary
    true true true true
    true true true true
    false false false false false false
    false false
    "kernel-check/evaluate the Lean 136-byte serializer and compare its complete output with the pinned dashiRTX coefficient bytes.  If equal, promote only the synthetic runtime-F ↔ Lean-F representation weld, then use the already-assembled Lean baseline action to attack the runtime-action equality.  Production CADO generator identity remains separate."
