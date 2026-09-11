module DASHI.ComputerScience.RSA260BidiFineIncidenceDefectCoverageExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260BidiFineIncidenceInterpolationExact as Interpolation
import DASHI.ComputerScience.RSA260BidiTwoHopCommonNeighbourFibreExact as TwoHop
import DASHI.ComputerScience.RSA260BlockWiedemannProductionScaleReconstructionExact as Scale
import DASHI.ComputerScience.RSA260CADOBlockWiedemannArtifactSchemaSnowballExact as CADO

------------------------------------------------------------------------
-- FINE-INCIDENCE DEFECT-COVERAGE BIDI EXPERIMENT
--
-- Refinement of the existing one-swap-per-row fragility owner.  Instead of
-- touching every row, hold the intervention strength at exactly one support
-- replacement per touched row and vary only COVERAGE across the carrier.
--
-- Preserve the complete coarse executable shadow contract:
--   924 x 512 over GF(2)
--   six degree-151 rows, 918 degree-150 rows
--   rank 512 / left-nullity 412
--   fixed CADO-shaped 4x4 preparation analogue
--   fixed projection seed.
--
-- touched rows : 0  1  2  4  8  16  32  64  128  256  512  924
-- degree       :16 16 17 18 18  20  23  30   46   63   66   65
--
-- Three independent perturbation seeds then replicate the middle/upper curve:
--   32  -> d=22..24
--   64  -> d=29..30
--   128 -> d=41..44
--   256 -> d=62..64
--   512 -> d=65..66
--   924 -> d=65..66
-- with all 18 replication runs preserving the kernel consumer.
--
-- This is a synthetic candidate experiment.  It does not measure fine
-- incidence on the historical RSA-260 matrix.
------------------------------------------------------------------------

interpolationBoundary : Interpolation.FineIncidenceFragilityBoundary
interpolationBoundary = Interpolation.canonicalFineIncidenceFragilityBoundary

twoHopBoundary : TwoHop.TwoHopInterpretationBoundary
twoHopBoundary = TwoHop.canonicalTwoHopInterpretationBoundary

productionScaleAtlas : Scale.ProductionScaleSourceAtlas
productionScaleAtlas = Scale.currentProductionScaleSourceAtlas

cadoArtifactSchema : CADO.CADOBlockWiedemannArtifactSchema
cadoArtifactSchema = CADO.currentCADOBlockWiedemannArtifactSchema

record DefectCoverageRuntimeSource : Set where
  constructor defect-coverage-runtime-source
  field
    repository : String
    branch : String
    path : String
    commit : String
    gitBlob : String
    dependencyPath : String
    dependencyGitBlob : String
    exactRuntimeBlobExecuted : Bool
    exactDependencyBlobExecuted : Bool
open DefectCoverageRuntimeSource public

currentDefectCoverageRuntimeSource : DefectCoverageRuntimeSource
currentDefectCoverageRuntimeSource = defect-coverage-runtime-source
  "chboishabba/dashiRTX"
  "agent/triadic-u8-runtime-oracle"
  "rsa260_bidi_fine_incidence_defect_coverage.py"
  "80750c1d9f9ea11bab3bf78ba62966d6961bd2d0"
  "777b261b7d76095b04a1ea2ae574439cd9d63144"
  "rsa260_bidi_candidate_robustness.py"
  "0f60c28f01b50c2337f2e5dec0016f918119371d"
  true true

record DefectCoverageReplicationRuntimeSource : Set where
  constructor defect-coverage-replication-runtime-source
  field
    repository : String
    branch : String
    path : String
    commit : String
    gitBlob : String
    coverageDependencyPath : String
    coverageDependencyGitBlob : String
    robustnessDependencyPath : String
    robustnessDependencyGitBlob : String
    exactTopLevelBlobExecuted : Bool
    exactCoverageDependencyBlobExecuted : Bool
    exactRobustnessDependencyBlobExecuted : Bool
open DefectCoverageReplicationRuntimeSource public

currentDefectCoverageReplicationRuntimeSource : DefectCoverageReplicationRuntimeSource
currentDefectCoverageReplicationRuntimeSource = defect-coverage-replication-runtime-source
  "chboishabba/dashiRTX"
  "agent/triadic-u8-runtime-oracle"
  "rsa260_bidi_defect_coverage_seed_replication.py"
  "a6817efde60810f81923ba16ca60e56fd1954e86"
  "b35659d5dcdb9070fa0c95722fc2dc38e1928a6f"
  "rsa260_bidi_fine_incidence_defect_coverage.py"
  "777b261b7d76095b04a1ea2ae574439cd9d63144"
  "rsa260_bidi_candidate_robustness.py"
  "0f60c28f01b50c2337f2e5dec0016f918119371d"
  true true true

record DefectCoverageReceipt : Set where
  constructor defect-coverage-receipt
  field
    carrierRows : Nat
    carrierColumns : Nat
    rowExcess : Nat
    interventionLevels : Nat
    supportReplacementsPerTouchedRow : Nat
    allLevelsFullRank : Bool
    allLevelsLeftNullity412 : Bool
    allLevelsRecoverConsumer : Bool
    baselineGeneratorDegree : Nat
    oneRowGeneratorDegree : Nat
    twoRowGeneratorDegree : Nat
    fourRowGeneratorDegree : Nat
    eightRowGeneratorDegree : Nat
    sixteenRowGeneratorDegree : Nat
    thirtyTwoRowGeneratorDegree : Nat
    sixtyFourRowGeneratorDegree : Nat
    oneHundredTwentyEightRowGeneratorDegree : Nat
    twoHundredFiftySixRowGeneratorDegree : Nat
    fiveHundredTwelveRowGeneratorDegree : Nat
    allRowsGeneratorDegree : Nat
    maximumObservedGeneratorDegree : Nat
open DefectCoverageReceipt public

currentDefectCoverageReceipt : DefectCoverageReceipt
currentDefectCoverageReceipt = defect-coverage-receipt
  924 512 412
  12
  1
  true true true
  16 16 17 18 18 20 23 30 46 63 66 65
  66

record DefectCoverageReplicationReceipt : Set where
  constructor defect-coverage-replication-receipt
  field
    coverageLevelsReplicated : Nat
    perturbationSeedsPerLevel : Nat
    totalReplicationRuns : Nat
    allReplicationRunsRecoverConsumer : Bool
    rows32MinimumDegree : Nat
    rows32MaximumDegree : Nat
    rows64MinimumDegree : Nat
    rows64MaximumDegree : Nat
    rows128MinimumDegree : Nat
    rows128MaximumDegree : Nat
    rows256MinimumDegree : Nat
    rows256MaximumDegree : Nat
    rows512MinimumDegree : Nat
    rows512MaximumDegree : Nat
    rows924MinimumDegree : Nat
    rows924MaximumDegree : Nat
    exactDegreeSeedInvariant : Bool
    coverageRegimeReplicated : Bool
open DefectCoverageReplicationReceipt public

currentDefectCoverageReplicationReceipt : DefectCoverageReplicationReceipt
currentDefectCoverageReplicationReceipt = defect-coverage-replication-receipt
  6 3 18 true
  22 24
  29 30
  41 44
  62 64
  65 66
  65 66
  false true

record DefectCoverageInterpretationBoundary : Set where
  constructor defect-coverage-interpretation-boundary
  field
    isolatedSingleRowDefectDestroysCompressibility : Bool
    oneSwapEveryRowDestroysTestedLowDegreePresentation : Bool
    broadDefectCoverageRaisesGeneratorComplexity : Bool
    coverageRegimeReplicatesAcrossSeeds : Bool
    exactGeneratorDegreeSeedInvariant : Bool
    coarseRankNullityExplainsObservedDegreeCurve : Bool
    consumerAdequacySurvivesEveryTestedCoverageLevel : Bool
    defectCoverageIsCandidateStructuralFibre : Bool
    oneHopAdjacencyMeanIsCompleteDegreePredictor : Bool
    twoHopPortfolioAlreadyPaidByPriorOwner : Bool
    syntheticCoverageCurveIsProductionMeasurement : Bool
    historicalMatrixIdentityPaid : Bool
open DefectCoverageInterpretationBoundary public

canonicalDefectCoverageInterpretationBoundary : DefectCoverageInterpretationBoundary
canonicalDefectCoverageInterpretationBoundary = defect-coverage-interpretation-boundary
  false
  true
  true
  true
  false
  false
  true
  true
  false
  true
  false
  false

------------------------------------------------------------------------
-- Snowball/identifier coordinates are inherited rather than recopied.
------------------------------------------------------------------------

scaleIdentityCoordinates : Scale.ProductionScaleIdentityCoordinates
scaleIdentityCoordinates = Scale.currentProductionScaleIdentityCoordinates

cadoSnowballCoordinates : CADO.CADOArtifactSnowballCoordinates
cadoSnowballCoordinates = CADO.currentCADOArtifactSnowballCoordinates

------------------------------------------------------------------------
-- Highest-alpha residuals after coverage replication.
------------------------------------------------------------------------

data DefectCoverageResidual : Set where
  crossValidateCoverageCurveAcrossPreparationAndProjectionFibres : DefectCoverageResidual
  fitCoverageAwareStructuralFibrePortfolio : DefectCoverageResidual
  measureCoverageFibresOnSameObjectProductionCarrier : DefectCoverageResidual

firstDefectCoverageResidual : DefectCoverageResidual
firstDefectCoverageResidual = crossValidateCoverageCurveAcrossPreparationAndProjectionFibres

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data SyntheticCoverageImpliesProductionCoverage : Set where
data OneStructuralFibreImpliesExactDegree : Set where
data SameRankNullityImpliesSameRecurrenceComplexity : Set where
data CoverageCurveImpliesUniversalThreshold : Set where
data ConsumerSurvivalImpliesHistoricalIdentity : Set where

syntheticCoverageDoesNotCreateProductionCoverage : SyntheticCoverageImpliesProductionCoverage → ⊥
syntheticCoverageDoesNotCreateProductionCoverage ()

oneStructuralFibreDoesNotCreateExactDegree : OneStructuralFibreImpliesExactDegree → ⊥
oneStructuralFibreDoesNotCreateExactDegree ()

sameRankNullityDoesNotCreateSameRecurrence : SameRankNullityImpliesSameRecurrenceComplexity → ⊥
sameRankNullityDoesNotCreateSameRecurrence ()

coverageCurveDoesNotCreateUniversalThreshold : CoverageCurveImpliesUniversalThreshold → ⊥
coverageCurveDoesNotCreateUniversalThreshold ()

consumerSurvivalDoesNotCreateHistoricalIdentity : ConsumerSurvivalImpliesHistoricalIdentity → ⊥
consumerSurvivalDoesNotCreateHistoricalIdentity ()
