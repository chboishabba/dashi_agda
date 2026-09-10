module DASHI.ComputerScience.RSA260ProjectionMatrixGeneratorExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260BlockWiedemannProjectionSequence256Exact as Projection
import DASHI.ComputerScience.RSA260ProjectionScalarBerlekampMasseyExact as ScalarBM
import DASHI.ComputerScience.RSA260GraphColouringF2PairProjectionCrossPollinationExact as Colouring

------------------------------------------------------------------------
-- FIRST SHARED MATRIX-POLYNOMIAL RECURRENCE OVER THE SYNTHETIC PROJECTION
--
-- Runtime/source-equivalent validation searches degrees d <= 32 for matrices
-- F_0 ... F_{d-1} in Mat_16(F_2) satisfying
--
--   S_{k+d} + sum_{l<d} S_{k+l} F_l = 0.
--
-- The first fitting degree is 17.  The recovered shared recurrence is fitted
-- on 367 training relations and then checked on 128 withheld relations.
-- This is strictly stronger than 256 unrelated entrywise scalar recurrences,
-- but it is NOT the CADO-NFS production minimal generator and does not use the
-- RSA-260 production sparse matrix or projection blocks.
------------------------------------------------------------------------

record MatrixGeneratorSourceReceipt : Set where
  constructor matrix-generator-source-receipt
  field
    repository : String
    branch : String
    path : String
    commitSha : String
    language : String
    projectionBlockSize : Nat
    sequenceTerms : Nat
    maximumSearchedDegree : Nat
open MatrixGeneratorSourceReceipt public

rsa260MatrixGeneratorSource : MatrixGeneratorSourceReceipt
rsa260MatrixGeneratorSource = matrix-generator-source-receipt
  "chboishabba/dashiRTX"
  "agent/triadic-u8-runtime-oracle"
  "rsa260_projection_matrix_generator_oracle.c"
  "e3d174d0e44d1eec0da0101d07921089e8471c59"
  "C11"
  16 512 32

record MatrixGeneratorExecutionReceipt : Set where
  constructor matrix-generator-execution-receipt
  field
    sourceEquivalentAlgebraValidated : Bool
    exactGitBlobExecuted : Bool
    firstFittingDegree : Nat
    unknownsPerOutputColumn : Nat
    trainingRelations : Nat
    withheldRelations : Nat
    sharedMatrixRecurrenceHoldsOnTraining : Bool
    sharedMatrixRecurrenceHoldsOnWithheld : Bool
    generatorDigest : String
    syntheticSequenceUsed : Bool
    productionRSA260SequenceUsed : Bool
    cadoMinimalGeneratorReproduced : Bool
    kernelVectorRecovered : Bool
open MatrixGeneratorExecutionReceipt public

rsa260MatrixGeneratorExecution : MatrixGeneratorExecutionReceipt
rsa260MatrixGeneratorExecution = matrix-generator-execution-receipt
  true
  false
  17
  272
  367
  128
  true
  true
  "3139b6bdee50b05a"
  true
  false
  false
  false

------------------------------------------------------------------------
-- Prior owners remain independent coordinates.
------------------------------------------------------------------------

projectionBoundary : Projection.RSA260ProjectionSequenceRoadmapBoundary
projectionBoundary = Projection.currentRSA260ProjectionSequenceRoadmapBoundary

scalarBMBoundary : ScalarBM.RSA260ScalarBMRoadmapBoundary
scalarBMBoundary = ScalarBM.currentRSA260ScalarBMRoadmapBoundary

colouringBoundary : Colouring.RSA260GraphColouringF2PairBoundary
colouringBoundary = Colouring.currentRSA260GraphColouringF2PairBoundary

------------------------------------------------------------------------
-- Roadmap boundary.
------------------------------------------------------------------------

record RSA260MatrixGeneratorRoadmapBoundary : Set where
  constructor rsa260-matrix-generator-roadmap-boundary
  field
    syntheticProjectionSequencePaid : Bool
    entrywiseScalarRecurrencesPaid : Bool
    sharedRightMatrixRecurrenceRecovered : Bool
    sharedRecurrenceValidatedOnWithheldTerms : Bool
    firstDegreeWithinSearchedAnsatzIdentified : Bool
    graphColouringDerivedBasisCovarianceAvailable : Bool
    productionMinimalGeneratorRecovered : Bool
    productionKernelVectorRecovered : Bool
    actualRSA260MatrixUsed : Bool
    cudaGeneratorReproduced : Bool
    ncclGeneratorReproduced : Bool
open RSA260MatrixGeneratorRoadmapBoundary public

currentRSA260MatrixGeneratorRoadmapBoundary : RSA260MatrixGeneratorRoadmapBoundary
currentRSA260MatrixGeneratorRoadmapBoundary = rsa260-matrix-generator-roadmap-boundary
  true true true true true true
  false false false false false

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data EntrywiseRecurrencesImplySharedGenerator : Set where
data SyntheticGeneratorImpliesProductionGenerator : Set where
data FirstFittingDegreeImpliesCanonicalMinimalGenerator : Set where
data GeneratorImpliesKernelVector : Set where
data BasisCovarianceImpliesGeneratorCorrectness : Set where

entrywiseDoesNotCreateSharedGenerator : EntrywiseRecurrencesImplySharedGenerator → ⊥
entrywiseDoesNotCreateSharedGenerator ()

syntheticDoesNotCreateProductionGenerator : SyntheticGeneratorImpliesProductionGenerator → ⊥
syntheticDoesNotCreateProductionGenerator ()

firstFitDoesNotCreateCanonicalMinimalGenerator : FirstFittingDegreeImpliesCanonicalMinimalGenerator → ⊥
firstFitDoesNotCreateCanonicalMinimalGenerator ()

generatorDoesNotCreateKernelVector : GeneratorImpliesKernelVector → ⊥
generatorDoesNotCreateKernelVector ()

basisCovarianceDoesNotCreateGeneratorCorrectness : BasisCovarianceImpliesGeneratorCorrectness → ⊥
basisCovarianceDoesNotCreateGeneratorCorrectness ()
