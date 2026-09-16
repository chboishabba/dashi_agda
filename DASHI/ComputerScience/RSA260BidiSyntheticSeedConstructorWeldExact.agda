module DASHI.ComputerScience.RSA260BidiSyntheticSeedConstructorWeldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260BidiRuntimeKrylovActionBindingExact as Runtime
import DASHI.ComputerScience.RSA260BidiSyntheticIncidenceConstructorWeldExact as Incidence

------------------------------------------------------------------------
-- SYNTHETIC SEED CONSTRUCTOR WELD
--
-- The baseline runtime seed V is deterministic rather than an acquired opaque
-- artifact.  dashiRTX builds each of its eight columns from BASEY xor (j<<32),
-- then fills 64-bit row chunks with the fixed wraparound mixer:
--
--   x ^= x >> 30
--   x *= 0xbf58476d1ce4e5b9
--   x ^= x >> 27
--   x *= 0x94d049bb133111eb
--   x ^= x >> 31.
--
-- Lean now source-defines the same finite constructor with BitVec 64, whose
-- multiplication, xor and logical shifts have the desired fixed-width
-- semantics.  As with the incidence matrix A, source-level formula agreement is
-- not silently promoted into a cross-language equality theorem.
------------------------------------------------------------------------

runtimeBoundary : Runtime.RuntimeKrylovActionBindingBoundary
runtimeBoundary = Runtime.canonicalRuntimeKrylovActionBindingBoundary

incidenceBoundary : Incidence.SyntheticIncidenceConstructorWeldBoundary
incidenceBoundary = Incidence.canonicalSyntheticIncidenceConstructorWeldBoundary

record LeanSyntheticSeedSourceReceipt : Set where
  constructor lean-synthetic-seed-source-receipt
  field
    repository : String
    branch : String
    regressionPath : String
    sourcePath : String
    wordTypeName : String
    mixName : String
    seedWordName : String
    seedBlockName : String
    redCommit : String
    sourceCommit : String
    rootIntegrationCommit : String
open LeanSyntheticSeedSourceReceipt public

currentLeanSyntheticSeedSourceReceipt : LeanSyntheticSeedSourceReceipt
currentLeanSyntheticSeedSourceReceipt =
  lean-synthetic-seed-source-receipt
    "chboishabba/dashi_lean4"
    "agent/rsa-consumer-kernel-bypass"
    "Synthesis/LinearConsumerSyntheticBidiSeedRegression.lean"
    "Synthesis/LinearConsumerSyntheticBidiSeed.lean"
    "Synthesis.SyntheticBidiWord"
    "Synthesis.syntheticBidiMix64"
    "Synthesis.syntheticBidiSeedWord"
    "Synthesis.syntheticBidiSeedBlock"
    "0550e6bcc9056c0a03838632d0c53950fb3fea81"
    "91c9378b1db0478cae080f5afe259c13cf712fc9"
    "0ac1b598cab01ae2936ca93062a808bd01cae725"

------------------------------------------------------------------------
-- Proof-relevant identity firewall.
------------------------------------------------------------------------

data RuntimeSeedEqualsLeanSeed : Set where

data RuntimeKrylovSetupEqualsLeanSetup : Set where
  runtime-krylov-setup-equals-lean :
    Incidence.RuntimeConstructorEqualsLeanConstructor ->
    RuntimeSeedEqualsLeanSeed ->
    RuntimeKrylovSetupEqualsLeanSetup

runtimeSeedIdentityStillUnpaid : RuntimeSeedEqualsLeanSeed -> ⊥
runtimeSeedIdentityStillUnpaid ()

setupRequiresSeedIdentity :
  RuntimeKrylovSetupEqualsLeanSetup -> RuntimeSeedEqualsLeanSeed
setupRequiresSeedIdentity
  (runtime-krylov-setup-equals-lean _ seedIdentity) = seedIdentity

record SyntheticSeedConstructorWeldBoundary : Set where
  constructor synthetic-seed-constructor-weld-boundary
  field
    runtimeSeedAlgorithmCommitted : Bool
    runtimeSeedDigestRetained : Bool
    runtimeSeedDimensionsRetained : Bool
    leanBitVec64CarrierUsed : Bool
    leanExactMixerSourceWritten : Bool
    leanExactSeedConstructorSourceWritten : Bool

    leanKernelReceiptObserved : Bool
    runtimeSeedBoundToLeanSeed : Bool
    runtimeIncidenceAndSeedJointSetupBound : Bool
    runtimeRecoveredFBoundToLeanF : Bool
    runtimeActionBoundToLeanKrylovAction : Bool
    twoVRuntimeKernelBoundToFormalJointKernel : Bool

    exactCADOMksolSemanticsPaid : Bool
    productionSameObjectCarrierPaid : Bool
open SyntheticSeedConstructorWeldBoundary public

canonicalSyntheticSeedConstructorWeldBoundary : SyntheticSeedConstructorWeldBoundary
canonicalSyntheticSeedConstructorWeldBoundary =
  synthetic-seed-constructor-weld-boundary
    true true true true true true
    false false false false false false
    false false

data SyntheticSeedConstructorResidual : Set where
  transportRuntimeSeedConstructorIntoLean : SyntheticSeedConstructorResidual
  combineIncidenceAndSeedConstructorPayments : SyntheticSeedConstructorResidual
  bindRecoveredCoefficientFamilyF : SyntheticSeedConstructorResidual
  bindRuntimeActionToLeanKrylovAction : SyntheticSeedConstructorResidual
  transportTwoVKernelToFormalJointKernel : SyntheticSeedConstructorResidual
  bindExactCADOMksolSemantics : SyntheticSeedConstructorResidual
  bindProductionSameObjectCarrier : SyntheticSeedConstructorResidual

firstSyntheticSeedConstructorResidual : SyntheticSeedConstructorResidual
firstSyntheticSeedConstructorResidual = transportRuntimeSeedConstructorIntoLean
