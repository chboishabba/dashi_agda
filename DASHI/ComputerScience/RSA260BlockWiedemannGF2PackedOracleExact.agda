module DASHI.ComputerScience.RSA260BlockWiedemannGF2PackedOracleExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260GNFSStageRunReceiptExact as Stage
import DASHI.ComputerScience.RSA260GNFSRunParameterArtifactSnowballExact as Params
import DASHI.ComputerScience.RSA260TriadicSWARExecutionRoadmapCrossPollinationExact as Roadmap

------------------------------------------------------------------------
-- FIRST RSA-STAGE-LOCAL EXECUTABLE ORACLE
--
-- The published RSA-260 Block Wiedemann lane reports width-256 sequences and
-- simd=256.  This owner binds a separate independent packed GF(2) primitive:
-- one 256-bit row and vector in four uint64_t words, with dot product equal to
-- parity(popcount(row & vector)).
--
-- The exact dashiRTX source blob was compiled under GCC 14.2.0 and checked by
-- 512 exact basis/disjoint cases plus 2^20 deterministic packed-vs-scalar
-- comparisons.  This pays the primitive only; it is not the RSA-260 matrix,
-- Krylov sequence, Block Wiedemann implementation, CUDA kernel, or run.
------------------------------------------------------------------------

record PackedGF2SourceReceipt : Set where
  constructor packed-gf2-source-receipt
  field
    repository : String
    branch : String
    path : String
    commitSha : String
    gitBlobSha : String
    language : String
    logicalWidthBits : Nat
    physicalCarrier : String
open PackedGF2SourceReceipt public

rsa260PackedGF2Source : PackedGF2SourceReceipt
rsa260PackedGF2Source = packed-gf2-source-receipt
  "chboishabba/dashiRTX"
  "agent/triadic-u8-runtime-oracle"
  "rsa260_block_wiedemann_gf2_packed_oracle.c"
  "4540d6e13c7d089545a1181f2f49c386449fb5bd"
  "1b533cd0504b57a809e4d73761bca5a631025b11"
  "C11"
  256
  "4 x uint64_t"

record PackedGF2ExecutionReceipt : Set where
  constructor packed-gf2-execution-receipt
  field
    exactSourceContentExecuted : Bool
    compiler : String
    compilerVersion : String
    compileFlags : String
    compilationSucceeded : Bool
    executionSucceeded : Bool
    logicalWidthBits : Nat
    exactBasisAndDisjointCases : Nat
    deterministicPackedVsScalarCases : Nat
    packedEqualsScalarOnCheckedCases : Bool
    actualRSA260MatrixUsed : Bool
    actualRSA260KrylovSequenceUsed : Bool
    actualLuDevinKernelUsed : Bool
    CUDAExecution : Bool
    NCCLExecution : Bool
    independentBlockWiedemannReproduction : Bool
    independentRSA260RunReproduction : Bool
open PackedGF2ExecutionReceipt public

rsa260PackedGF2Execution : PackedGF2ExecutionReceipt
rsa260PackedGF2Execution = packed-gf2-execution-receipt
  true
  "gcc"
  "14.2.0"
  "-std=c11 -O3 -Wall -Wextra -pedantic"
  true true
  256
  512
  1048576
  true
  false false false false false false false

rsaLinearAlgebraRun : Stage.StageRunReceipt
rsaLinearAlgebraRun = Stage.rsa260LinearAlgebraRun

rsaLinearAlgebraParameters : Params.RunParameterReceipt
rsaLinearAlgebraParameters = Params.rsa260LinearAlgebraParameters

priorRoadmap : Roadmap.RSA260ExecutionRoadmapBoundary
priorRoadmap = Roadmap.currentRSA260ExecutionRoadmapBoundary

record RSA260BlockWiedemannRoadmapBoundary : Set where
  constructor rsa260-block-wiedemann-roadmap-boundary
  field
    width256PrimaryParameterRetained : Bool
    packedGF2Dot256Executable : Bool
    packedGF2DotComparedAgainstScalarOracle : Bool
    exactRSA260SparseMatrixAcquired : Bool
    matrixVectorMultiplyKernelReproduced : Bool
    krylovIterationReproduced : Bool
    blockWiedemannSequenceReproduced : Bool
    cudaWidth256KernelReproduced : Bool
    ncclCommunicationReproduced : Bool
    fullLinearAlgebraStageReproduced : Bool
    fullRSA260RunReproduced : Bool
open RSA260BlockWiedemannRoadmapBoundary public

currentRSA260BlockWiedemannRoadmapBoundary : RSA260BlockWiedemannRoadmapBoundary
currentRSA260BlockWiedemannRoadmapBoundary = rsa260-block-wiedemann-roadmap-boundary
  true true true
  false false false false false false false false

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data Width256PrimitiveImpliesRSA260Matrix : Set where
data GF2DotImpliesBlockWiedemann : Set where
data PackedCPUImpliesSIMD256 : Set where
data PackedCPUImpliesCUDA : Set where
data PrimitiveReproductionImpliesStageReproduction : Set where
data StagePrimitiveImpliesFactorizationReproduction : Set where

widthDoesNotCreateMatrixIdentity : Width256PrimitiveImpliesRSA260Matrix → ⊥
widthDoesNotCreateMatrixIdentity ()

gf2DotDoesNotCreateBlockWiedemann : GF2DotImpliesBlockWiedemann → ⊥
gf2DotDoesNotCreateBlockWiedemann ()

packedCPUDoesNotCreateSIMD256 : PackedCPUImpliesSIMD256 → ⊥
packedCPUDoesNotCreateSIMD256 ()

packedCPUDoesNotCreateCUDA : PackedCPUImpliesCUDA → ⊥
packedCPUDoesNotCreateCUDA ()

primitiveDoesNotReproduceStage : PrimitiveReproductionImpliesStageReproduction → ⊥
primitiveDoesNotReproduceStage ()

stagePrimitiveDoesNotReproduceFactorization : StagePrimitiveImpliesFactorizationReproduction → ⊥
stagePrimitiveDoesNotReproduceFactorization ()
