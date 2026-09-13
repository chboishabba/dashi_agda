module DASHI.ComputerScience.RSA260KrylovKernelRecoveryExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260ProjectionMatrixGeneratorExact as Generator
import DASHI.ComputerScience.RSA260BlockWiedemannProjectionSequence256Exact as Projection

------------------------------------------------------------------------
-- SYNTHETIC KRYLOV RELATION -> NONZERO KERNEL VECTOR
--
-- The degree-17 matrix generator from the projected sequence is first lifted
-- back to the full 256-dimensional Krylov carrier.  Separately, the shifted
-- relation space among K_l = M^l Y, l=1..17, is solved directly.  Shifting any
-- such relation back one power gives a candidate v with Mv=0; acceptance
-- requires v to be nonzero.
--
-- This pays the synthetic kernel-recovery step only.  It does NOT identify the
-- RSA-260 production matrix, CADO-NFS's production recovery code, or the final
-- RSA-260 dependency vector.
------------------------------------------------------------------------

record KrylovLiftSourceReceipt : Set where
  constructor krylov-lift-source-receipt
  field
    repository : String
    branch : String
    path : String
    commitSha : String
    gitBlobSha : String
    language : String
open KrylovLiftSourceReceipt public

krylovLiftSource : KrylovLiftSourceReceipt
krylovLiftSource = krylov-lift-source-receipt
  "chboishabba/dashiRTX"
  "agent/triadic-u8-runtime-oracle"
  "rsa260_projection_generator_krylov_lift_oracle.c"
  "71c643f6a3eea34b7f8a180f60012db3986e7369"
  "abb129b599fc33c0ee2acc0f980cc176853210dc"
  "C11"

record KernelRecoverySourceReceipt : Set where
  constructor kernel-recovery-source-receipt
  field
    repository : String
    branch : String
    path : String
    commitSha : String
    gitBlobSha : String
    language : String
open KernelRecoverySourceReceipt public

kernelRecoverySource : KernelRecoverySourceReceipt
kernelRecoverySource = kernel-recovery-source-receipt
  "chboishabba/dashiRTX"
  "agent/triadic-u8-runtime-oracle"
  "rsa260_krylov_kernel_recovery_oracle.c"
  "011230549541d95c646e0556392e29209af9eb8a"
  "f04651f6fd3e1e39a0b350231ad80dbeee2283d7"
  "C11"

record KrylovLiftExecutionReceipt : Set where
  constructor krylov-lift-execution-receipt
  field
    sourceEquivalentAlgebraValidation : Bool
    exactGitBlobExecuted : Bool
    generatorDegree : Nat
    generatorLiftsToVectorBlockRelation : Bool
    residualZeroColumns : Nat
    residualRank : Nat
    residualWeight : Nat
    actualRSA260MatrixUsed : Bool
open KrylovLiftExecutionReceipt public

krylovLiftExecution : KrylovLiftExecutionReceipt
krylovLiftExecution = krylov-lift-execution-receipt
  true false
  17
  true
  16
  0
  0
  false

record KernelRecoveryExecutionReceipt : Set where
  constructor kernel-recovery-execution-receipt
  field
    sourceEquivalentAlgebraValidation : Bool
    exactGitBlobExecuted : Bool
    ambientDimension : Nat
    matrixRank : Nat
    matrixNullity : Nat
    shiftedKrylovColumns : Nat
    shiftedRelationSpaceDimension : Nat
    nonzeroKernelRelationsFound : Nat
    chosenFreeColumn : Nat
    chosenRelationWeight : Nat
    recoveredKernelVectorWeight : Nat
    recoveredKernelVectorNonzero : Bool
    recoveredKernelVectorSatisfiesMvZero : Bool
    deterministicKernelDigest : String
    productionRSA260KernelRecovered : Bool
open KernelRecoveryExecutionReceipt public

kernelRecoveryExecution : KernelRecoveryExecutionReceipt
kernelRecoveryExecution = kernel-recovery-execution-receipt
  true false
  256
  255
  1
  272
  17
  10
  254
  132
  116
  true
  true
  "f8b6694d1696c20f"
  false

------------------------------------------------------------------------
-- Existing generator/projection owners remain separate coordinates.
------------------------------------------------------------------------

generatorBoundary : Generator.RSA260MatrixGeneratorRoadmapBoundary
generatorBoundary = Generator.currentRSA260MatrixGeneratorRoadmapBoundary

projectionBoundary : Projection.RSA260ProjectionSequenceRoadmapBoundary
projectionBoundary = Projection.currentRSA260ProjectionSequenceRoadmapBoundary

------------------------------------------------------------------------
-- Roadmap boundary after synthetic kernel recovery.
------------------------------------------------------------------------

record RSA260KrylovKernelRecoveryRoadmapBoundary : Set where
  constructor rsa260-krylov-kernel-recovery-roadmap-boundary
  field
    syntheticProjectionSequenceExecutable : Bool
    sharedMatrixGeneratorRecovered : Bool
    sharedGeneratorLiftsToFullKrylovRelation : Bool
    shiftedKrylovRelationSpaceSolved : Bool
    nonzeroSyntheticKernelVectorRecovered : Bool
    recoveredVectorVerifiedByDirectMatVec : Bool
    syntheticMatrixRankAndNullityMeasured : Bool
    exactRSA260MatrixAcquired : Bool
    productionGeneratorRecovered : Bool
    productionKernelVectorRecovered : Bool
    cudaKernelRecoveryReproduced : Bool
    ncclKernelRecoveryReproduced : Bool
    fullRSA260LinearAlgebraStageReproduced : Bool
open RSA260KrylovKernelRecoveryRoadmapBoundary public

currentRSA260KrylovKernelRecoveryRoadmapBoundary : RSA260KrylovKernelRecoveryRoadmapBoundary
currentRSA260KrylovKernelRecoveryRoadmapBoundary =
  rsa260-krylov-kernel-recovery-roadmap-boundary
    true true true true true true true
    false false false false false false

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data ProjectedRelationImpliesVectorRelation : Set where
data VectorRelationImpliesNonzeroKernelVector : Set where
data ZeroCandidateImpliesRecoveryFailure : Set where
data SyntheticKernelImpliesRSA260Kernel : Set where
data Rank255SyntheticImpliesProductionNullity : Set where
data KernelRecoveryImpliesCUDA : Set where

projectedRelationDoesNotAutomaticallyLift : ProjectedRelationImpliesVectorRelation → ⊥
projectedRelationDoesNotAutomaticallyLift ()

vectorRelationDoesNotAutomaticallyGiveNonzeroKernel : VectorRelationImpliesNonzeroKernelVector → ⊥
vectorRelationDoesNotAutomaticallyGiveNonzeroKernel ()

zeroCandidateDoesNotMeanRelationSpaceFailed : ZeroCandidateImpliesRecoveryFailure → ⊥
zeroCandidateDoesNotMeanRelationSpaceFailed ()

syntheticKernelDoesNotCreateRSA260Kernel : SyntheticKernelImpliesRSA260Kernel → ⊥
syntheticKernelDoesNotCreateRSA260Kernel ()

syntheticNullityDoesNotCreateProductionNullity : Rank255SyntheticImpliesProductionNullity → ⊥
syntheticNullityDoesNotCreateProductionNullity ()

kernelRecoveryDoesNotCreateCUDA : KernelRecoveryImpliesCUDA → ⊥
kernelRecoveryDoesNotCreateCUDA ()
