module DASHI.Biology.IITHyperfabricCompletionReceiptExact where

open import DASHI.Core.Prelude

import DASHI.Biology.IIT4FiniteExecutableKernelExact as Kernel
import DASHI.Biology.IITXORGridFibreCalibrationExact as Grid
import DASHI.Biology.IITMatchedFabricGateExperimentExact as Matched
import DASHI.Biology.IIT369MatchedAlgebraControlExact as Algebra
import DASHI.Biology.IITHyperfabricCausalCellNetworkExact as Fabric
import DASHI.Biology.IITPointed27HyperformExperimentExact as Pointed
import DASHI.Biology.IIT4FiniteCauseEffectStructureExact as Structure
import DASHI.Biology.IITXOR369StressFamilyExact as Stress
import DASHI.Biology.IITIIT4ConsumerDescentExact as Consumer

------------------------------------------------------------------------
-- TERMINAL COMPLETION LEDGER
--
-- Verification authorities are deliberately separated:
--
--   * Agda imports + kernel checking establish the formal theorem surface.
--   * Python is used only for executable numerical / finite-combinatorial
--     verification of IIT fixtures and reference calculations.
--   * PyPhi is an external numerical oracle for full distinction/relation/CES
--     calculations; its results are not Agda proofs.
--
-- No Python or grep-based source checker is part of this authority chain.
------------------------------------------------------------------------

data VerificationLevel : Set where
  sourceWritten : VerificationLevel
  numericVerificationProgramPresent : VerificationLevel
  numericVerificationExecuted : VerificationLevel
  externalOracleAdapterPresent : VerificationLevel
  agdaKernelVerified : VerificationLevel

record CompletionLedger : Set where
  constructor completionLedger
  field
    task1VersionedSystemKernelSource : Bool
    task2XorGridCalibrationSource : Bool
    task3MatchedFabricGateSource : Bool
    task4Matched369AlgebraSource : Bool
    task5HyperformFabricSource : Bool
    task6Pointed27GluingSource : Bool
    task7DistinctionRelationStructureSource : Bool
    task7PyPhiFullStructureAdapterPresent : Bool
    task8Xor369StressSource : Bool
    task9ConsumerDescentSource : Bool
    task10ReceiptLoopSource : Bool

    numericVerificationProgramExists : Bool
    numericVerificationExecutedInThisEnvironment : Bool
    fullPyPhiOracleExecutedInThisEnvironment : Bool
    agdaKernelExecutedInThisEnvironment : Bool

    formalVerificationAuthority : String
    numericVerificationProgram : String
    externalOracleAdapter : String
    kernelVerificationReceipt : String

open CompletionLedger public

currentCompletionLedger : CompletionLedger
currentCompletionLedger =
  completionLedger
    true true true true true true true true true true true
    true true false false
    "agda DASHI/EverythingIITPhiIntegrationMaxCut.agda"
    "scripts/iit_numeric_verification.py; numerical and finite-combinatorial verification only"
    "scripts/iit4_pyphi_oracle.py; full CES numerical oracle when PyPhi is installed"
    "PENDING: Agda kernel has not been executed in this execution environment"

allTenSourceTasksPresent :
  task1VersionedSystemKernelSource currentCompletionLedger ≡ true
  × task2XorGridCalibrationSource currentCompletionLedger ≡ true
  × task3MatchedFabricGateSource currentCompletionLedger ≡ true
  × task4Matched369AlgebraSource currentCompletionLedger ≡ true
  × task5HyperformFabricSource currentCompletionLedger ≡ true
  × task6Pointed27GluingSource currentCompletionLedger ≡ true
  × task7DistinctionRelationStructureSource currentCompletionLedger ≡ true
  × task8Xor369StressSource currentCompletionLedger ≡ true
  × task9ConsumerDescentSource currentCompletionLedger ≡ true
  × task10ReceiptLoopSource currentCompletionLedger ≡ true
allTenSourceTasksPresent =
  refl , refl , refl , refl , refl , refl , refl , refl , refl , refl

fullStructureAdapterPresent :
  task7PyPhiFullStructureAdapterPresent currentCompletionLedger ≡ true
fullStructureAdapterPresent = refl

numericProgramPresent :
  numericVerificationProgramExists currentCompletionLedger ≡ true
numericProgramPresent = refl

numericVerificationWasExecuted :
  numericVerificationExecutedInThisEnvironment currentCompletionLedger ≡ true
numericVerificationWasExecuted = refl

noFakeKernelPromotion :
  agdaKernelExecutedInThisEnvironment currentCompletionLedger ≡ false
noFakeKernelPromotion = refl

noFakePyPhiExecutionClaim :
  fullPyPhiOracleExecutedInThisEnvironment currentCompletionLedger ≡ false
noFakePyPhiExecutionClaim = refl

kernelBoundary : Kernel.IIT4ExecutableKernelBoundary
kernelBoundary = Kernel.canonicalIIT4ExecutableKernelBoundary

gridReceipt : Grid.XORGridCalibrationReceipt
gridReceipt = Grid.currentXORGridCalibrationReceipt

matchedReceipt : Matched.MatchedSweepReceipt
matchedReceipt = Matched.currentMatchedSweepReceipt

algebraReceipt : Algebra.AlgebraControlReceipt
algebraReceipt = Algebra.currentAlgebraControlReceipt

fabricReceipt : Fabric.HyperfabricFixtureReceipt
fabricReceipt = Fabric.currentHyperfabricFixtureReceipt

pointedReceipt : Pointed.Pointed27ScanReceipt
pointedReceipt = Pointed.currentPointed27ScanReceipt

stressReceipt : Stress.StressFamilyReceipt
stressReceipt = Stress.currentStressFamilyReceipt

consumerBoundary : Consumer.IITConsumerDescentBoundary
consumerBoundary = Consumer.canonicalIITConsumerDescentBoundary

structureBoundary : Structure.IIT4CauseEffectStructureBoundary
structureBoundary = Structure.canonicalIIT4CauseEffectStructureBoundary
