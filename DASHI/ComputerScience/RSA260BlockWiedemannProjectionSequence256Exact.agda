module DASHI.ComputerScience.RSA260BlockWiedemannProjectionSequence256Exact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260BlockWiedemannGF2PackedOracleExact as Dot
import DASHI.ComputerScience.RSA260DNA256BlockStructureCrossPollinationExact as DNA256
import DASHI.ComputerScience.RSA260BlockWiedemannSparseMatVec256Exact as SpMV
import DASHI.ComputerScience.RSA260BlockWiedemannKrylov256Exact as Krylov

------------------------------------------------------------------------
-- FIRST BLOCK-WIEDEMANN-SHAPED PROJECTION SEQUENCE ORACLE
--
-- The runtime owner computes, for a deterministic synthetic sparse GF(2)
-- matrix M and deterministic 256 x 16 blocks X,Y,
--
--   S_k = X^T M^k Y
--
-- as a 16 x 16 GF(2) projection matrix for 32 consecutive sequence terms.
-- Every projected entry and every column Krylov update is compared between the
-- packed 4 x 64 implementation and a bit-by-bit scalar oracle.
--
-- This pays the projection-sequence SHAPE and independent synthetic execution,
-- not the RSA-260 matrix, not the published m=n=512 geometry, not the two
-- width-256 production sequences, not a minimal generator, and not the final
-- Block Wiedemann solve.
------------------------------------------------------------------------

record ProjectionSequenceSourceReceipt : Set where
  constructor projection-sequence-source-receipt
  field
    repository : String
    branch : String
    path : String
    commitSha : String
    gitBlobSha : String
    language : String
    ambientWidth : Nat
    carrierBlocks : Nat
    coordinatesPerBlock : Nat
    leftBlockColumns : Nat
    rightBlockColumns : Nat
    sequenceTerms : Nat
open ProjectionSequenceSourceReceipt public

rsa260ProjectionSequenceSource : ProjectionSequenceSourceReceipt
rsa260ProjectionSequenceSource = projection-sequence-source-receipt
  "chboishabba/dashiRTX"
  "agent/triadic-u8-runtime-oracle"
  "rsa260_block_wiedemann_projection_sequence_256_oracle.c"
  "83aa9a86fa56ae80436660120fdcbae3f0c3b939"
  "13cf8bc4496018de2464b293cc6bac4ed4089028"
  "C11"
  256 4 64 16 16 32

record ProjectionSequenceExecutionReceipt : Set where
  constructor projection-sequence-execution-receipt
  field
    sourceEquivalentExecutionPassed : Bool
    exactGitBlobExecuted : Bool
    compiler : String
    compilerVersion : String
    compileFlags : String
    compilationSucceeded : Bool
    executionSucceeded : Bool
    projectionEntriesChecked : Nat
    krylovColumnStepsChecked : Nat
    packedProjectionEqualsScalar : Bool
    packedKrylovEqualsScalar : Bool
    deterministicDigest : String
    syntheticMatrixUsed : Bool
    actualRSA260MatrixUsed : Bool
    published512By512GeometryReproduced : Bool
    publishedTwoWidth256SequencesReproduced : Bool
    minimalGeneratorComputed : Bool
    fullBlockWiedemannSolveReproduced : Bool
    CUDAExecution : Bool
    NCCLExecution : Bool
open ProjectionSequenceExecutionReceipt public

rsa260ProjectionSequenceExecution : ProjectionSequenceExecutionReceipt
rsa260ProjectionSequenceExecution = projection-sequence-execution-receipt
  true
  false
  "gcc"
  "14.2.0"
  "-std=c11 -O3 -Wall -Wextra -pedantic"
  true true
  8192
  512
  true true
  "ba9dd735c50e236a"
  true
  false false false false false false false

------------------------------------------------------------------------
-- Prior paid execution layers remain separate owners.
------------------------------------------------------------------------

packedDotReceipt : Dot.PackedGF2ExecutionReceipt
packedDotReceipt = Dot.rsa260PackedGF2Execution

dna256Boundary : DNA256.RSA260DNA256BlockStructureBoundary
dna256Boundary = DNA256.canonicalRSA260DNA256BlockStructureBoundary

sparseMatVecBoundary : SpMV.RSA260SparseMatVecRoadmapBoundary
sparseMatVecBoundary = SpMV.currentRSA260SparseMatVecRoadmapBoundary

krylovBoundary : Krylov.RSA260KrylovRoadmapBoundary
krylovBoundary = Krylov.currentRSA260KrylovRoadmapBoundary

------------------------------------------------------------------------
-- Roadmap boundary after the projection-sequence tranche.
------------------------------------------------------------------------

record RSA260ProjectionSequenceRoadmapBoundary : Set where
  constructor rsa260-projection-sequence-roadmap-boundary
  field
    width256PackedDotExecutable : Bool
    syntheticSparseMatVecExecutable : Bool
    syntheticKrylovRecurrenceExecutable : Bool
    blockProjectionFormulaInstantiated : Bool
    syntheticProjectionSequenceExecutable : Bool
    projectionCheckedAgainstScalar : Bool
    exactRSA260MatrixAcquired : Bool
    publishedBlockGeometryReproduced : Bool
    productionProjectionVectorsAcquired : Bool
    productionProjectionSequenceReproduced : Bool
    minimalGeneratorReproduced : Bool
    kernelVectorRecovered : Bool
    cudaProjectionSequenceReproduced : Bool
    ncclProjectionSequenceReproduced : Bool
    fullLinearAlgebraStageReproduced : Bool
open RSA260ProjectionSequenceRoadmapBoundary public

currentRSA260ProjectionSequenceRoadmapBoundary : RSA260ProjectionSequenceRoadmapBoundary
currentRSA260ProjectionSequenceRoadmapBoundary = rsa260-projection-sequence-roadmap-boundary
  true true true true true true
  false false false false false false false false false

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data SmallProjectionImpliesPublishedGeometry : Set where
data SyntheticProjectionImpliesProductionSequence : Set where
data ProjectionSequenceImpliesMinimalGenerator : Set where
data MinimalGeneratorImpliesKernelVector : Set where
data PackedCPUProjectionImpliesCUDA : Set where
data DNA256BlockShapeImpliesBlockWiedemannAlgebra : Set where

data SameProjectionDigestImpliesSameRun : Set where

smallProjectionDoesNotCreatePublishedGeometry : SmallProjectionImpliesPublishedGeometry → ⊥
smallProjectionDoesNotCreatePublishedGeometry ()

syntheticProjectionDoesNotCreateProductionSequence : SyntheticProjectionImpliesProductionSequence → ⊥
syntheticProjectionDoesNotCreateProductionSequence ()

projectionSequenceDoesNotCreateGenerator : ProjectionSequenceImpliesMinimalGenerator → ⊥
projectionSequenceDoesNotCreateGenerator ()

generatorDoesNotAutomaticallyRecoverKernelVector : MinimalGeneratorImpliesKernelVector → ⊥
generatorDoesNotAutomaticallyRecoverKernelVector ()

packedCPUProjectionDoesNotCreateCUDA : PackedCPUProjectionImpliesCUDA → ⊥
packedCPUProjectionDoesNotCreateCUDA ()

dnaBlockShapeDoesNotCreateBWAlgebra : DNA256BlockShapeImpliesBlockWiedemannAlgebra → ⊥
dnaBlockShapeDoesNotCreateBWAlgebra ()

sameDigestDoesNotIdentifyRun : SameProjectionDigestImpliesSameRun → ⊥
sameDigestDoesNotIdentifyRun ()
