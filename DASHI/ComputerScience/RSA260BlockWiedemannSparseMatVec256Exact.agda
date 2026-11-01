module DASHI.ComputerScience.RSA260BlockWiedemannSparseMatVec256Exact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260BlockWiedemannGF2PackedOracleExact as Dot
import DASHI.ComputerScience.RSA260DNA256BlockStructureCrossPollinationExact as DNA256

------------------------------------------------------------------------
-- FIRST RECOGNIZABLE RSA BLOCK-WIEDEMANN-ADJACENT MATRIX KERNEL
--
-- A synthetic sparse 256 x 256 GF(2) matrix is represented row-wise, with each
-- row stored as four uint64_t words. Matrix-vector application is explicitly
-- traversed as four blocks of 64 output coordinates. This reuses the already
-- paid packed dot256 primitive and the DNA-derived structural 4 x 64 partition
-- discipline, while importing no biological alphabet or algebra.
--
-- The exact dashiRTX Git blob was compiled with GCC 14.2.0 and checked against
-- a scalar bit-by-bit oracle over 65,792 matrix-vector cases.
------------------------------------------------------------------------

record SparseMatVec256SourceReceipt : Set where
  constructor sparse-matvec-256-source-receipt
  field
    repository : String
    branch : String
    path : String
    commitSha : String
    gitBlobSha : String
    language : String
    rows : Nat
    columns : Nat
    outerBlocks : Nat
    coordinatesPerBlock : Nat
    rowCarrier : String
open SparseMatVec256SourceReceipt public

rsa260SparseMatVec256Source : SparseMatVec256SourceReceipt
rsa260SparseMatVec256Source = sparse-matvec-256-source-receipt
  "chboishabba/dashiRTX"
  "agent/triadic-u8-runtime-oracle"
  "rsa260_block_wiedemann_sparse_matvec_256_oracle.c"
  "e13a26a075e2dc0751dd91332c38d9545343a306"
  "4312f7fb0a9703f7fea0c2318f2099aa090eddd6"
  "C11"
  256 256 4 64
  "each row = 4 x uint64_t; output vector = 4 x uint64_t"

record SparseMatVec256ExecutionReceipt : Set where
  constructor sparse-matvec-256-execution-receipt
  field
    exactGitBlobExecuted : Bool
    compiler : String
    compilerVersion : String
    compileFlags : String
    compilationSucceeded : Bool
    executionSucceeded : Bool
    identityBasisCases : Nat
    syntheticSparseMatrices : Nat
    deterministicVectorsPerMatrix : Nat
    totalMatrixVectorChecks : Nat
    packedEqualsScalarOnAllCheckedCases : Bool
    fourBySixtyFourTraversalUsed : Bool
    priorDot256PrimitiveReusedSemantically : Bool
    actualRSA260MatrixUsed : Bool
    actualRSA260KrylovVectorUsed : Bool
    cudaExecution : Bool
    ncclExecution : Bool
    independentBlockWiedemannReproduction : Bool
open SparseMatVec256ExecutionReceipt public

rsa260SparseMatVec256Execution : SparseMatVec256ExecutionReceipt
rsa260SparseMatVec256Execution = sparse-matvec-256-execution-receipt
  true
  "gcc"
  "14.2.0"
  "-std=c11 -O3 -Wall -Wextra -pedantic"
  true true
  256 256 256 65792
  true true true
  false false false false false

priorDotExecution : Dot.PackedGF2ExecutionReceipt
priorDotExecution = Dot.rsa260PackedGF2Execution

priorDNA256Boundary : DNA256.DNA256RSA260RoadmapBoundary
priorDNA256Boundary = DNA256.currentDNA256RSA260RoadmapBoundary

record RSA260SparseMatVecRoadmapBoundary : Set where
  constructor rsa260-sparse-matvec-roadmap-boundary
  field
    packedDot256Paid : Bool
    structuralFourBySixtyFourPartitionPaid : Bool
    syntheticSparseMatVec256Paid : Bool
    packedVsScalarMatVecAgreementPaid : Bool
    actualRSA260SparseMatrixAcquired : Bool
    actualRSA260SpMVReproduced : Bool
    oneKrylovStepOnRSA260MatrixReproduced : Bool
    blockWiedemannSequenceReproduced : Bool
    cudaKernelReproduced : Bool
    fullLinearAlgebraStageReproduced : Bool
open RSA260SparseMatVecRoadmapBoundary public

currentRSA260SparseMatVecRoadmapBoundary : RSA260SparseMatVecRoadmapBoundary
currentRSA260SparseMatVecRoadmapBoundary = rsa260-sparse-matvec-roadmap-boundary
  true true true true
  false false false false false false

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data SyntheticSparseMatrixImpliesRSA260Matrix : Set where
data SameFourBySixtyFourShapeImpliesSameMatrix : Set where
data DNA256StructureImpliesGF2Semantics : Set where
data SparseMatVecImpliesKrylovSequence : Set where
data CPUOracleImpliesCUDAReproduction : Set where

syntheticDoesNotCreateRSA260Matrix : SyntheticSparseMatrixImpliesRSA260Matrix → ⊥
syntheticDoesNotCreateRSA260Matrix ()

sameBlockShapeDoesNotIdentifyMatrix : SameFourBySixtyFourShapeImpliesSameMatrix → ⊥
sameBlockShapeDoesNotIdentifyMatrix ()

dnaStructureDoesNotCreateGF2Semantics : DNA256StructureImpliesGF2Semantics → ⊥
dnaStructureDoesNotCreateGF2Semantics ()

matVecDoesNotCreateKrylovSequence : SparseMatVecImpliesKrylovSequence → ⊥
matVecDoesNotCreateKrylovSequence ()

cpuOracleDoesNotCreateCUDAReceipt : CPUOracleImpliesCUDAReproduction → ⊥
cpuOracleDoesNotCreateCUDAReceipt ()
