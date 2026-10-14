module DASHI.Biology.IITHyperfabricCompletionReceiptExact where

open import DASHI.Core.Prelude

import DASHI.Biology.IIT4FiniteExecutableKernelExact as Kernel
import DASHI.Biology.IITXORGridFibreCalibrationExact as Grid
import DASHI.Biology.IITMatchedFabricGateExperimentExact as Matched
import DASHI.Biology.IIT369MatchedAlgebraControlExact as Algebra
import DASHI.Biology.IITHyperfabricCausalCellNetworkExact as Fabric
import DASHI.Biology.IITPointed27HyperformExperimentExact as Pointed
import DASHI.Biology.IIT4FiniteDistinctionExact as Distinction
import DASHI.Biology.IIT4FiniteRelationExact as Relation
import DASHI.Biology.IIT4FiniteCauseEffectStructureExact as Structure
import DASHI.Biology.IITXOR369StressFamilyExact as Stress
import DASHI.Biology.IITIIT4ConsumerDescentExact as Consumer

------------------------------------------------------------------------
-- TERMINAL COMPLETION LEDGER
------------------------------------------------------------------------

data VerificationLevel : Set where
  sourceWritten : VerificationLevel
  pythonReferenceVerified : VerificationLevel
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

    localPythonReferenceChecksExecutable : Bool
    fullPyPhiOracleExecutedInThisEnvironment : Bool
    agdaKernelExecutedInThisEnvironment : Bool

    sourceCompletionReceipt : String
    pythonCompletionChecker : String
    externalOracleAdapter : String
    kernelVerificationReceipt : String

open CompletionLedger public

currentCompletionLedger : CompletionLedger
currentCompletionLedger =
  completionLedger
    true true true true true true true true true true true
    true false false
    "tasks 1-10 source surfaces imported by IITHyperfabricCompletionReceiptExact"
    "scripts/check_iit_hyperfabric_completion.py"
    "scripts/iit4_pyphi_oracle.py; requires an installed PyPhi runtime"
    "PENDING: no Agda executable or CI kernel receipt available in this execution environment"

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
