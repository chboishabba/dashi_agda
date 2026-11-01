module DASHI.ComputerScience.RSA260BidiCandidateGeneratorKernelExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.RobustExperimentInferenceFrontierExact as Experiment
import DASHI.ComputerScience.RSA260BidiCandidateBWCShadowExact as Shadow
import DASHI.ComputerScience.RSA260ProjectionMatrixGeneratorExact as Generator
import DASHI.ComputerScience.RSA260KrylovKernelRecoveryExact as Kernel

------------------------------------------------------------------------
-- CANDIDATE-DERIVED PROJECTION -> GENERATOR -> KERNEL EXPERIMENT
--
-- The sequence is generated from the repaired bidi candidate shadow through
-- the experimental B = A A^T adapter.  The shared matrix recurrence is fitted
-- on a training prefix and validated on withheld terms.  Shifted Krylov
-- relations are then solved independently and the recovered nonzero vector is
-- required to satisfy both B y = 0 and A^T y = 0.
--
-- This certifies the candidate construction for these declared consumers.
-- It does NOT identify the historical RSA-260 matrix, CADO preparation,
-- production width-256 generator, or production dependency vector.
------------------------------------------------------------------------

shadowBoundary : Shadow.PreparedShadowConsumerBoundary
shadowBoundary = Shadow.canonicalPreparedShadowConsumerBoundary

generatorBoundary : Generator.RSA260MatrixGeneratorRoadmapBoundary
generatorBoundary = Generator.currentRSA260MatrixGeneratorRoadmapBoundary

kernelBoundary : Kernel.RSA260KrylovKernelRecoveryRoadmapBoundary
kernelBoundary = Kernel.currentRSA260KrylovKernelRecoveryRoadmapBoundary

experimentBoundary : Experiment.RobustExperimentFrontierBoundary
experimentBoundary = Experiment.canonicalRobustExperimentFrontierBoundary

record CandidateGeneratorKernelRuntimeSource : Set where
  constructor candidate-generator-kernel-runtime-source
  field
    repository : String
    branch : String
    path : String
    commit : String
    gitBlob : String
    compiler : String
    exactGitBlobExecuted : Bool
open CandidateGeneratorKernelRuntimeSource public

currentCandidateGeneratorKernelRuntimeSource : CandidateGeneratorKernelRuntimeSource
currentCandidateGeneratorKernelRuntimeSource = candidate-generator-kernel-runtime-source
  "chboishabba/dashiRTX"
  "agent/triadic-u8-runtime-oracle"
  "rsa260_bidi_candidate_generator_kernel_oracle.c"
  "6e730784a79ad2d5145a318bd60aa2625af9c4ec"
  "2b7c5ab262b220594381ecdaba2a0dc0552ad5c3"
  "gcc -std=c11 -O2 -Wall -Wextra -pedantic"
  true

record CandidateGeneratorExecutionReceipt : Set where
  constructor candidate-generator-execution-receipt
  field
    projectionBlockWidth : Nat
    sequenceTerms : Nat
    firstFittingDegree : Nat
    trainingRelations : Nat
    withheldRelations : Nat
    sharedRecurrenceHoldsOnTraining : Bool
    sharedRecurrenceHoldsOnWithheld : Bool
    generatorDigest : String
    productionWidth256GeneratorPaid : Bool
    productionGeneratorLength1281607Paid : Bool
open CandidateGeneratorExecutionReceipt public

currentCandidateGeneratorExecutionReceipt : CandidateGeneratorExecutionReceipt
currentCandidateGeneratorExecutionReceipt = candidate-generator-execution-receipt
  8 256 17 175 64
  true true
  "c9f9583f0c38bb80"
  false false

record CandidateKernelExecutionReceipt : Set where
  constructor candidate-kernel-execution-receipt
  field
    shiftedKrylovColumns : Nat
    shiftedRelationSpaceDimension : Nat
    nonzeroKernelRelationsFound : Nat
    chosenFreeColumn : Nat
    chosenRelationWeight : Nat
    recoveredKernelWeight : Nat
    recoveredKernelDigest : String
    recoveredKernelNonzero : Bool
    recoveredKernelSatisfiesPreparedZero : Bool
    recoveredKernelSatisfiesOriginalATZero : Bool
    productionDependencyRecovered : Bool
open CandidateKernelExecutionReceipt public

currentCandidateKernelExecutionReceipt : CandidateKernelExecutionReceipt
currentCandidateKernelExecutionReceipt = candidate-kernel-execution-receipt
  136 16 16 119 54 436
  "82d61e3ce9eda8d5"
  true true true
  false

record CandidateFullLAConsumerBoundary : Set where
  constructor candidate-full-la-consumer-boundary
  field
    candidateProjectionSequencePaid : Bool
    candidateSharedGeneratorPaid : Bool
    candidateGeneratorWithheldValidationPaid : Bool
    candidateShiftedRelationSpacePaid : Bool
    candidateNonzeroKernelRecoveryPaid : Bool
    candidatePreparedKernelDirectlyVerified : Bool
    candidateOriginalRectangularLeftKernelVerified : Bool
    fullCandidateCPUConsumerChainPaid : Bool
    historicalSameObjectIdentityPaid : Bool
    productionPreparedEncodingPaid : Bool
    productionWidth256ProjectionPaid : Bool
    productionGeneratorPaid : Bool
    productionDependencyPaid : Bool
open CandidateFullLAConsumerBoundary public

canonicalCandidateFullLAConsumerBoundary : CandidateFullLAConsumerBoundary
canonicalCandidateFullLAConsumerBoundary = candidate-full-la-consumer-boundary
  true true true true true true true true
  false false false false false

------------------------------------------------------------------------
-- Next experiment escalation.
------------------------------------------------------------------------

data CandidateFullLAResidual : Set where
  raiseProjectionWidthToward256 : CandidateFullLAResidual
  compareIndependentProjectionSeeds : CandidateFullLAResidual
  compareAlternativePreparedAdapters : CandidateFullLAResidual
  measureCandidateCompressionCostFrontier : CandidateFullLAResidual
  validateAgainstSameObjectProductionArtifact : CandidateFullLAResidual

firstCandidateFullLAResidual : CandidateFullLAResidual
firstCandidateFullLAResidual = raiseProjectionWidthToward256

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data CandidateGeneratorImpliesProductionGenerator : Set where
data CandidateKernelImpliesProductionDependency : Set where
data WithheldRecurrenceImpliesHistoricalIdentity : Set where
data AATKernelImpliesCADOPreparedKernel : Set where

candidateGeneratorDoesNotCreateProductionGenerator : CandidateGeneratorImpliesProductionGenerator → ⊥
candidateGeneratorDoesNotCreateProductionGenerator ()

candidateKernelDoesNotCreateProductionDependency : CandidateKernelImpliesProductionDependency → ⊥
candidateKernelDoesNotCreateProductionDependency ()

withheldRecurrenceDoesNotCreateHistoricalIdentity : WithheldRecurrenceImpliesHistoricalIdentity → ⊥
withheldRecurrenceDoesNotCreateHistoricalIdentity ()

aatKernelDoesNotCreateCADOPreparedKernel : AATKernelImpliesCADOPreparedKernel → ⊥
aatKernelDoesNotCreateCADOPreparedKernel ()
