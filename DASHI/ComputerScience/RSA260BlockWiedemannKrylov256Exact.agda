module DASHI.ComputerScience.RSA260BlockWiedemannKrylov256Exact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260BlockWiedemannSparseMatVec256Exact as SpMV
import DASHI.ComputerScience.RSA260DNA256BlockStructureCrossPollinationExact as DNA256

------------------------------------------------------------------------
-- SYNTHETIC KRYLOV RECURRENCE OVER THE PAID 4x64 GF(2) CARRIER
--
-- This owner advances the synthetic sparse 256x256 SpMV oracle by iterating
-- x_(k+1) = M x_k.  Packed 4x64 execution is compared step-by-step with the
-- bit-by-bit scalar GF(2) oracle.
--
-- The runtime source lives in dashiRTX as
--   rsa260_block_wiedemann_krylov_256_oracle.c
-- on branch agent/triadic-u8-runtime-oracle, commit
--   af5b605b91363cd46bd9d75675a578ede9916125
-- blob
--   5ad172a215402fe4cef7746ca9f8452677477016
--
-- A source-equivalent local compilation/execution passed 64 matrices x 128
-- recurrence steps = 8192 packed-vs-scalar checks with deterministic digest
-- 7be887e054f07f0b.  Exact Git-blob byte identity was not independently bound
-- in that local execution, so exactGitBlobExecuted remains false.
------------------------------------------------------------------------

record KrylovSourceReceipt : Set where
  constructor krylov-source-receipt
  field
    repository : String
    branch : String
    path : String
    commitSha : String
    gitBlobSha : String
    language : String
open KrylovSourceReceipt public

krylovSource : KrylovSourceReceipt
krylovSource = krylov-source-receipt
  "chboishabba/dashiRTX"
  "agent/triadic-u8-runtime-oracle"
  "rsa260_block_wiedemann_krylov_256_oracle.c"
  "af5b605b91363cd46bd9d75675a578ede9916125"
  "5ad172a215402fe4cef7746ca9f8452677477016"
  "C11"

record KrylovExecutionReceipt : Set where
  constructor krylov-execution-receipt
  field
    logicalWidthBits : Nat
    blockCount : Nat
    coordinatesPerBlock : Nat
    matrixCases : Nat
    stepsPerMatrix : Nat
    checkedRecurrenceSteps : Nat
    packedEqualsScalarOnCheckedSteps : Bool
    deterministicSequenceDigest : String
    sourceEquivalentExecutionPassed : Bool
    exactGitBlobExecuted : Bool
    actualRSA260MatrixUsed : Bool
    actualRSA260InitialBlockUsed : Bool
    actualRSA260KrylovSequenceUsed : Bool
    blockWiedemannProjectionSequenceBuilt : Bool
    minimalGeneratorSolved : Bool
    CUDAExecution : Bool
    NCCLExecution : Bool
    independentRSA260LinearAlgebraReproduction : Bool
open KrylovExecutionReceipt public

krylovExecution : KrylovExecutionReceipt
krylovExecution = krylov-execution-receipt
  256 4 64
  64 128 8192
  true
  "7be887e054f07f0b"
  true
  false
  false false false false false false false false

priorSparseMatVec : SpMV.RSA260SparseMatVecRoadmapBoundary
priorSparseMatVec = SpMV.currentRSA260SparseMatVecRoadmapBoundary

dna256Structure : DNA256.DNA256RSA260RoadmapBoundary
dna256Structure = DNA256.currentDNA256RSA260RoadmapBoundary

record RSA260KrylovRoadmapBoundary : Set where
  constructor rsa260-krylov-roadmap-boundary
  field
    fourBy64CarrierRetained : Bool
    syntheticSparseSpMVAvailable : Bool
    repeatedKrylovRecurrenceExecuted : Bool
    packedRecurrenceComparedAgainstScalar : Bool
    actualRSA260MatrixAcquired : Bool
    actualRSA260KrylovSequenceReproduced : Bool
    blockProjectionSequenceReproduced : Bool
    minimalGeneratorReproduced : Bool
    cudaKrylovReproduced : Bool
    ncclKrylovTransportReproduced : Bool
    fullBlockWiedemannReproduced : Bool
open RSA260KrylovRoadmapBoundary public

currentRSA260KrylovRoadmapBoundary : RSA260KrylovRoadmapBoundary
currentRSA260KrylovRoadmapBoundary = rsa260-krylov-roadmap-boundary
  true true true true
  false false false false false false false

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data KrylovRecurrenceImpliesBlockWiedemann : Set where
data SyntheticKrylovImpliesRSA260Sequence : Set where
data SequenceDigestImpliesExactSourceIdentity : Set where
data Same4x64CarrierImpliesSameAlgebra : Set where

krylovRecurrenceDoesNotCompleteBlockWiedemann : KrylovRecurrenceImpliesBlockWiedemann → ⊥
krylovRecurrenceDoesNotCompleteBlockWiedemann ()

syntheticKrylovDoesNotCreateRSA260Sequence : SyntheticKrylovImpliesRSA260Sequence → ⊥
syntheticKrylovDoesNotCreateRSA260Sequence ()

digestDoesNotBindExactSource : SequenceDigestImpliesExactSourceIdentity → ⊥
digestDoesNotBindExactSource ()

sameBlockShapeDoesNotIdentifyAlgebra : Same4x64CarrierImpliesSameAlgebra → ⊥
sameBlockShapeDoesNotIdentifyAlgebra ()
