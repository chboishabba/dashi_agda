module DASHI.ComputerScience.RSA260ProjectionScalarBerlekampMasseyExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260BlockWiedemannProjectionSequence256Exact as Projection
import DASHI.ComputerScience.RSA260GraphColouringF2PairProjectionCrossPollinationExact as ColourF2

------------------------------------------------------------------------
-- ENTRYWISE BERLEKAMP-MASSEY DIAGNOSTIC OVER THE SYNTHETIC PROJECTION SEQUENCE
--
-- The paired runtime generates 512 terms of a synthetic 16 x 16 projection
-- sequence S_k = X^T M^k Y and runs ordinary scalar Berlekamp-Massey over GF(2)
-- independently on each of its 256 bit-valued entry sequences.
--
-- Every recovered scalar recurrence is replayed against all 512 available
-- terms. This pays entrywise recurrence recovery only. It does NOT construct
-- the block/matrix minimal generator required by Block Wiedemann and does not
-- recover a kernel vector or reproduce the RSA-260 production sequence.
------------------------------------------------------------------------

record ScalarBMSourceReceipt : Set where
  constructor scalar-bm-source-receipt
  field
    repository : String
    branch : String
    path : String
    commitSha : String
    language : String
open ScalarBMSourceReceipt public

scalarBMSource : ScalarBMSourceReceipt
scalarBMSource = scalar-bm-source-receipt
  "chboishabba/dashiRTX"
  "agent/triadic-u8-runtime-oracle"
  "rsa260_projection_scalar_berlekamp_massey_oracle.c"
  "285eb9d0f16865c543480b9542c0deb85ca49aba"
  "C11"

record ScalarBMExecutionReceipt : Set where
  constructor scalar-bm-execution-receipt
  field
    projectionRows : Nat
    projectionColumns : Nat
    scalarEntrySequences : Nat
    termsPerSequence : Nat
    allRecoveredRecurrencesReplay : Bool
    minimumRecoveredDegree : Nat
    maximumRecoveredDegree : Nat
    sumRecoveredDegrees : Nat
    degreeDigest : String
    sourceEquivalentExecutionPassed : Bool
    exactGitBlobExecuted : Bool
    matrixMinimalGeneratorComputed : Bool
    kernelVectorRecovered : Bool
    actualRSA260SequenceUsed : Bool
open ScalarBMExecutionReceipt public

scalarBMExecution : ScalarBMExecutionReceipt
scalarBMExecution = scalar-bm-execution-receipt
  16 16 256 512
  true
  244 255 64230
  "420a4a7d22f04b19"
  true
  false
  false false false

priorProjection : Projection.RSA260ProjectionSequenceRoadmapBoundary
priorProjection = Projection.currentRSA260ProjectionSequenceRoadmapBoundary

colourBasisInvariant : ColourF2.GraphColouringRSAProjectionBoundary
colourBasisInvariant = ColourF2.currentGraphColouringRSAProjectionBoundary

record RSA260ScalarBMRoadmapBoundary : Set where
  constructor rsa260-scalar-bm-roadmap-boundary
  field
    syntheticProjectionSequencePaid : Bool
    f2PairBasisMetamorphicTestPaid : Bool
    all256ScalarEntryRecurrencesRecovered : Bool
    recoveredRecurrencesReplayed : Bool
    scalarDegreesNearAmbientWidthObserved : Bool
    blockMatrixMinimalGeneratorPaid : Bool
    kernelRelationPaid : Bool
    actualRSA260ProjectionSequencePaid : Bool
    entrywiseBMUsefulAsDiagnostic : Bool
    entrywiseBMSufficientForBlockWiedemann : Bool
open RSA260ScalarBMRoadmapBoundary public

currentRSA260ScalarBMRoadmapBoundary : RSA260ScalarBMRoadmapBoundary
currentRSA260ScalarBMRoadmapBoundary = rsa260-scalar-bm-roadmap-boundary
  true true true true true
  false false false
  true false

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data ScalarRecurrencesImpliesMatrixMinimalGenerator : Set where
data HighScalarDegreeImpliesRSAHardness : Set where
data RecurrenceReplayImpliesKernelVector : Set where
data ColourBasisInvariantImpliesSolverCorrectness : Set where
data SyntheticBMImpliesProductionBM : Set where

scalarBMDoesNotConstructMatrixGenerator : ScalarRecurrencesImpliesMatrixMinimalGenerator → ⊥
scalarBMDoesNotConstructMatrixGenerator ()

highDegreeDoesNotProveRSAHardness : HighScalarDegreeImpliesRSAHardness → ⊥
highDegreeDoesNotProveRSAHardness ()

replayDoesNotRecoverKernelVector : RecurrenceReplayImpliesKernelVector → ⊥
replayDoesNotRecoverKernelVector ()

basisInvariantDoesNotProveSolver : ColourBasisInvariantImpliesSolverCorrectness → ⊥
basisInvariantDoesNotProveSolver ()

syntheticDoesNotBecomeProduction : SyntheticBMImpliesProductionBM → ⊥
syntheticDoesNotBecomeProduction ()
