module DASHI.Biology.ExceptionalLatticeGrokkingProtocolExact where

open import DASHI.Core.Prelude

import DASHI.Biology.SpectralGrokkingLatticeExact as Grokking

------------------------------------------------------------------------
-- Fixed benchmark data for falsifiable representation-geometry comparisons.
-- These constants identify the dimensions and minimal-vector counts of the
-- E8 and Leech lattice kissing configurations; no trained-network match is
-- inferred from the constants alone.

minimalVectorCount : Grokking.ExceptionalLattice → Nat
minimalVectorCount Grokking.E8Lattice = 240
minimalVectorCount Grokking.LeechLattice = 196560

E8MinimalVectorCountIsTwoHundredForty :
  minimalVectorCount Grokking.E8Lattice ≡ 240
E8MinimalVectorCountIsTwoHundredForty = refl

LeechMinimalVectorCountIsOneHundredNinetySixThousandFiveHundredSixty :
  minimalVectorCount Grokking.LeechLattice ≡ 196560
LeechMinimalVectorCountIsOneHundredNinetySixThousandFiveHundredSixty = refl

record ExceptionalLatticeBenchmark : Set where
  constructor exceptionalLatticeBenchmark
  field
    lattice : Grokking.ExceptionalLattice
    ambientDimension : Nat
    shortestVectorCount : Nat
    dimensionCertificate : ambientDimension ≡ Grokking.latticeDimension lattice
    vectorCountCertificate : shortestVectorCount ≡ minimalVectorCount lattice

open ExceptionalLatticeBenchmark public

E8Benchmark : ExceptionalLatticeBenchmark
E8Benchmark = exceptionalLatticeBenchmark Grokking.E8Lattice 8 240 refl refl

LeechBenchmark : ExceptionalLatticeBenchmark
LeechBenchmark =
  exceptionalLatticeBenchmark Grokking.LeechLattice 24 196560 refl refl

------------------------------------------------------------------------
-- Experiment protocol.  Every comparison must fix the representation carrier,
-- energy family, task loss, null models, metric, and held-out evaluation before
-- observing a putative exceptional-lattice resemblance.

data PotentialFamily : Set where
  gaussianPotential : PotentialFamily
  inversePowerPotential : PotentialFamily
  declaredCustomPotential : PotentialFamily

data GeometryMetric : Set where
  gramMatrixMetric : GeometryMetric
  distanceSpectrumMetric : GeometryMetric
  angleSpectrumMetric : GeometryMetric
  symmetryCharacterMetric : GeometryMetric

data NullGeometry : Set where
  randomSphericalCode : NullGeometry
  cyclicFourierCode : NullGeometry
  rootLatticeA : NullGeometry
  rootLatticeD : NullGeometry

record GrokkingGeometryProtocol : Set where
  constructor grokkingGeometryProtocol
  field
    embeddingDimensionFixedBeforeTraining : Bool
    potentialFamilyDeclaredBeforeTraining : Bool
    taskLossDeclared : Bool
    geometryMetricDeclared : Bool
    nullGeometriesDeclared : Bool
    heldOutEvaluationDeclared : Bool
    seedAndOptimizationTraceRecorded : Bool
    multipleComparisonsControlled : Bool

open GrokkingGeometryProtocol public

canonicalPreregisteredGeometryProtocol : GrokkingGeometryProtocol
canonicalPreregisteredGeometryProtocol =
  grokkingGeometryProtocol true true true true true true true true

incompletePostHocGeometryProtocol : GrokkingGeometryProtocol
incompletePostHocGeometryProtocol =
  grokkingGeometryProtocol false false true false false false false false

record GeometryExperiment : Set where
  constructor geometryExperiment
  field
    benchmark : ExceptionalLatticeBenchmark
    potential : PotentialFamily
    metric : GeometryMetric
    nullModelCount : Nat
    protocol : GrokkingGeometryProtocol
    observedScore : Nat
    heldOutScore : Nat

open GeometryExperiment public

unrunE8Comparison : GeometryExperiment
unrunE8Comparison =
  geometryExperiment
    E8Benchmark
    gaussianPotential
    gramMatrixMetric
    4
    canonicalPreregisteredGeometryProtocol
    0
    0

unrunLeechComparison : GeometryExperiment
unrunLeechComparison =
  geometryExperiment
    LeechBenchmark
    gaussianPotential
    distanceSpectrumMetric
    4
    canonicalPreregisteredGeometryProtocol
    0
    0

------------------------------------------------------------------------
-- Candidate energy bookkeeping.  This records the declared decomposition of
-- representation energy without pretending to solve the continuous optimizer.

record RepresentationEnergy : Set where
  constructor representationEnergy
  field
    pairPotentialEnergy : Nat
    taskLossEnergy : Nat
    regularizationEnergy : Nat

open RepresentationEnergy public

totalRepresentationEnergy : RepresentationEnergy → Nat
totalRepresentationEnergy energy =
  pairPotentialEnergy energy
  + taskLossEnergy energy
  + regularizationEnergy energy

canonicalCandidateEnergy : RepresentationEnergy
canonicalCandidateEnergy = representationEnergy 8 3 1

canonicalCandidateTotalEnergyIsTwelve :
  totalRepresentationEnergy canonicalCandidateEnergy ≡ 12
canonicalCandidateTotalEnergyIsTwelve = refl

record ExceptionalLatticeGrokkingBoundary : Set where
  constructor exceptionalLatticeGrokkingBoundary
  field
    universalOptimalityImpliesEveryGrokkingRepresentationIsE8OrLeech : Bool
    universalOptimalityImpliesEveryGrokkingRepresentationIsE8OrLeechIsFalse :
      universalOptimalityImpliesEveryGrokkingRepresentationIsE8OrLeech ≡ false

    matchingDimensionAndVectorCountProvesLatticeIsometry : Bool
    matchingDimensionAndVectorCountProvesLatticeIsometryIsFalse :
      matchingDimensionAndVectorCountProvesLatticeIsometry ≡ false

    postHocSimilarityIsAValidPreRegisteredTest : Bool
    postHocSimilarityIsAValidPreRegisteredTestIsFalse :
      postHocSimilarityIsAValidPreRegisteredTest ≡ false

    exceptionalLatticesProvideRigorousBenchmarkTargets : Bool
    exceptionalLatticesProvideRigorousBenchmarkTargetsIsTrue :
      exceptionalLatticesProvideRigorousBenchmarkTargets ≡ true

open ExceptionalLatticeGrokkingBoundary public

canonicalExceptionalLatticeGrokkingBoundary : ExceptionalLatticeGrokkingBoundary
canonicalExceptionalLatticeGrokkingBoundary =
  exceptionalLatticeGrokkingBoundary false refl false refl false refl true refl
