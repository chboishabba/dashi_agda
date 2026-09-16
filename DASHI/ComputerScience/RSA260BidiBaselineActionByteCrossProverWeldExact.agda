module DASHI.ComputerScience.RSA260BidiBaselineActionByteCrossProverWeldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260BidiSeedByteCrossProverWeldExact as Seed

------------------------------------------------------------------------
-- BASELINE ACTION-BYTE CROSS-PROVER WELD FRONTIER
--
-- Runtime and Lean now each expose one canonical byte per row for the fully
-- assembled 924x8 synthetic baseline action.  The Lean bytes are derived from
-- `syntheticBidiBaselineAction`; the runtime bytes are derived from the same
-- hash-bound executable action whose stored and streaming evaluations agree.
--
-- This is the finite representation frontier.  Source availability and shared
-- representation do not themselves establish a Lean kernel-certified equality.
------------------------------------------------------------------------

seedBoundary : Seed.SeedByteCrossProverWeldBoundary
seedBoundary = Seed.canonicalSeedByteCrossProverWeldBoundary

record BaselineActionByteSourceReceipt : Set where
  constructor baseline-action-byte-source-receipt
  field
    runtimeRepository : String
    runtimeBranch : String
    runtimeSourceCommit : String
    runtimeProducerPath : String
    runtimeRegressionPath : String
    runtimeByteCount : Nat
    runtimeActionRowBytesSHA256 : String
    runtimeFirst16Hex : String
    runtimeLast16Hex : String

    leanRepository : String
    leanBranch : String
    leanBaselineActionPath : String
    leanActionBytesRegressionPath : String
    leanActionBytesPath : String
    leanActionBytesRedCommit : String
    leanActionBytesSourceCommit : String
    leanActionBytesRootCommit : String
open BaselineActionByteSourceReceipt public

currentBaselineActionByteSourceReceipt : BaselineActionByteSourceReceipt
currentBaselineActionByteSourceReceipt =
  baseline-action-byte-source-receipt
    "chboishabba/dashiRTX"
    "agent/triadic-u8-runtime-oracle"
    "3b7fdd6fce355373caf3a47ae47c5b58c9ff27d7"
    "rsa260_bidi_mksol_action_binding.py"
    "test_rsa260_bidi_action_row_bytes.py"
    924
    "51c708216fd1f0b73d8d18d856fb60197488c107df20d8ab6481c27179ad69e1"
    "9f7077d364b3cb29243668b433c8fd44"
    "48605d7e71aceb12698e69509cce128e"
    "chboishabba/dashi_lean4"
    "agent/rsa-consumer-kernel-bypass"
    "Synthesis/LinearConsumerSyntheticBidiBaselineAction.lean"
    "Synthesis/LinearConsumerSyntheticBidiBaselineActionBytesRegression.lean"
    "Synthesis/LinearConsumerSyntheticBidiBaselineActionBytes.lean"
    "58b0c043a944b988de6e5245a6d518c355e002a6"
    "c76e578e9d3f5c4c84cd032a02b9a8232889a89f"
    "4413cb455d5264db64cabe0356f74dd3d0112a4c"

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data ActionByteSourcesCreateKernelEquality : Set where
data SyntheticActionEqualityCreatesCADOSemantics : Set where

actionByteSourcesDoNotCreateKernelEquality : ActionByteSourcesCreateKernelEquality -> ⊥
actionByteSourcesDoNotCreateKernelEquality ()

syntheticActionEqualityDoesNotCreateCADOSemantics :
  SyntheticActionEqualityCreatesCADOSemantics -> ⊥
syntheticActionEqualityDoesNotCreateCADOSemantics ()

record BaselineActionByteCrossProverWeldBoundary : Set where
  constructor baseline-action-byte-cross-prover-weld-boundary
  field
    runtimeActionBytesExplicitlyRetained : Bool
    runtimeActionByteCountIs924 : Bool
    runtimeActionBytesHashRetained : Bool
    runtimeActionByteRegressionWritten : Bool

    leanConcreteBaselineActionSourceWritten : Bool
    leanBaselineActionByteSerializerDerivedStructurally : Bool
    leanActionByteRegressionWritten : Bool
    commonActionRowByteConventionRecorded : Bool

    runtimeActionBytesComparedToLeanBytes : Bool
    leanKernelReceiptObserved : Bool
    runtimeActionBoundToLeanBaselineAction : Bool
    runtimeTwoVKernelBoundToFormalJointKernel : Bool

    exactCADOMksolSemanticsPaid : Bool
    productionSameObjectActionPaid : Bool
    nextResidual : String
open BaselineActionByteCrossProverWeldBoundary public

canonicalBaselineActionByteCrossProverWeldBoundary :
  BaselineActionByteCrossProverWeldBoundary
canonicalBaselineActionByteCrossProverWeldBoundary =
  baseline-action-byte-cross-prover-weld-boundary
    true true true true
    true true true true
    false false false false
    false false
    "execute/evaluate the Lean concrete baseline-action serializer and compare all 924 bytes with the pinned runtime action bytes.  With a Lean kernel receipt and the already-localized coefficient/seed/operator bindings, promote only the synthetic runtime-action ↔ Lean-baseline-action weld; then transport the checked two-V runtime zero-kernel matrix into the formal jointKernel theorem. Production CADO mksol semantics remain a separate lane."
