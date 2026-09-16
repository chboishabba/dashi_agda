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
-- A dashiRTX crosscheck source now pins the exact Lean fixture commit and the
-- exact runtime producer commit and compares those 136 bytes.  That checker is
-- source-written here, but no execution receipt for the exact committed checker
-- is promoted by this owner.
--
-- Source agreement and an intended common convention are not a Lean kernel
-- theorem or production same-object identity.
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
    runtimeCrosscheckRegressionPath : String
    runtimeCrosscheckPath : String
    runtimeCrosscheckRedCommit : String
    runtimeCrosscheckSourceCommit : String

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
    "000000000000000048480048484848488d5e681991b956ba9ecf127bd9c3402f149d07f109827ffc74c77c54eb2f0ff73e86c7e4655b2423764903ed69d18482a77a93909d8940e8aa606979f949c0233bf6207175d6e49ec94f905edb01a69a2b6a0ca90a1f6ee740e77e71033f36b1a922f45c7d6582ad213da4146ada00005300000000000000"
    "test_rsa260_bidi_lean_coefficient_fixture_crosscheck.py"
    "rsa260_bidi_lean_coefficient_fixture_crosscheck.py"
    "2d80de8901ca8e3e79279bd59ae8eb88ccf8068d"
    "bcb4aba313ce6def6e2c79f47116a7f1ce9236ac"
    "chboishabba/dashi_lean4"
    "agent/rsa-consumer-kernel-bypass"
    "1e3542098a6a644a6d0916d4286d33e8b92f366b"
    "Synthesis/LinearConsumerSyntheticBidiCoefficients.lean"
    "Synthesis/LinearConsumerSyntheticBidiCoefficientBytesRegression.lean"
    "Synthesis/LinearConsumerSyntheticBidiCoefficientBytes.lean"
    "5da10473cff3d6d2163293ced86b6dbeab8037a1"
    "332ad62036712a34a472234b5f0170f73c1c27de"
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
    pinnedFiniteCrosscheckSourceWritten : Bool

    leanCoefficientFixtureSourceWritten : Bool
    leanCanonical136ByteSerializerSourceWritten : Bool
    leanByteRegressionWritten : Bool
    commonRowMajorConventionRecorded : Bool

    exactCommittedCrosscheckExecuted : Bool
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
    true true true true true
    true true true true
    false false false false false false false
    false false
    "execute the exact committed dashiRTX finite crosscheck and obtain a Lean kernel receipt for the 136-byte serializer.  Only then promote the synthetic runtime-F ↔ Lean-F representation weld.  Next, compare the already-assembled Lean baseline action against the hash-bound runtime action; production CADO generator identity remains separate."
