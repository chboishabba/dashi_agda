module DASHI.ComputerScience.RSA260BidiFineIncidenceDefectCoverageExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260BidiFineIncidencePredictorExact as Predictor
import DASHI.ComputerScience.RSA260BlockWiedemannProductionScaleReconstructionExact as Scale
import DASHI.ComputerScience.RSA260CADOBlockWiedemannArtifactSchemaSnowballExact as CADO

------------------------------------------------------------------------
-- FINE-INCIDENCE DEFECT-COVERAGE BIDI EXPERIMENT
--
-- Preserve the complete coarse executable shadow contract:
--   924 x 512 over GF(2)
--   six degree-151 rows, 918 degree-150 rows
--   rank 512 / left-nullity 412
--   fixed CADO-shaped 4x4 preparation analogue
--   fixed projection seed.
--
-- Intervention: replace exactly one support coordinate in an increasing
-- number of rows.  The first held-out-valid shared-generator degrees are:
--
-- touched rows : 0  1  2  4  8  16  32  64  128  256  512  924
-- degree       :16 16 17 18 18  20  23  30   46   63   66   65
--
-- Therefore recurrence compressibility is robust to isolated local defects
-- but degrades with defect COVERAGE across the carrier, while rank/nullity and
-- the eventual kernel consumer remain unchanged.
--
-- This is a synthetic candidate experiment.  It does not measure fine
-- incidence on the historical RSA-260 matrix.
------------------------------------------------------------------------

predictorBoundary : Predictor.FineIncidencePredictorBoundary
predictorBoundary = Predictor.canonicalFineIncidencePredictorBoundary

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
    baselineTouchedRows : Nat
    baselineGeneratorDegree : Nat
    oneRowGeneratorDegree : Nat
    twoRowGeneratorDegree : Nat
    fourRowGeneratorDegree : Nat
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
  0 16
  16 17 18
  20 23 30 46 63 66 65
  66

record DefectCoverageInterpretationBoundary : Set where
  constructor defect-coverage-interpretation-boundary
  field
    isolatedSingleRowDefectDestroysCompressibility : Bool
    broadDefectCoverageRaisesGeneratorComplexity : Bool
    coarseRankNullityExplainsObservedDegreeCurve : Bool
    consumerAdequacySurvivesEveryTestedCoverageLevel : Bool
    defectCoverageIsCandidateStructuralFibre : Bool
    adjacencyMeanAloneIsCompleteDegreePredictor : Bool
    syntheticCoverageCurveIsProductionMeasurement : Bool
    historicalMatrixIdentityPaid : Bool
open DefectCoverageInterpretationBoundary public

canonicalDefectCoverageInterpretationBoundary : DefectCoverageInterpretationBoundary
canonicalDefectCoverageInterpretationBoundary = defect-coverage-interpretation-boundary
  false
  true
  false
  true
  true
  false
  false
  false

------------------------------------------------------------------------
-- Snowball/identifier boundary inherited from the source-paid owners.
------------------------------------------------------------------------

scaleIdentityCoordinates : Scale.ProductionScaleIdentityCoordinates
scaleIdentityCoordinates = Scale.currentProductionScaleIdentityCoordinates

cadoSnowballCoordinates : CADO.CADOArtifactSnowballCoordinates
cadoSnowballCoordinates = CADO.currentCADOArtifactSnowballCoordinates

------------------------------------------------------------------------
-- Highest-alpha residuals.
------------------------------------------------------------------------

data DefectCoverageResidual : Set where
  replicateCoverageCurveAcrossPerturbationSeeds : DefectCoverageResidual
  addTwoHopAndCommonNeighbourCoverageFibres : DefectCoverageResidual
  fitConsumerRelativeRecurrenceComplexityModel : DefectCoverageResidual
  measureCoverageFibresOnSameObjectProductionCarrier : DefectCoverageResidual

firstDefectCoverageResidual : DefectCoverageResidual
firstDefectCoverageResidual = replicateCoverageCurveAcrossPerturbationSeeds

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data SyntheticCoverageImpliesProductionCoverage : Set where
data OneStructuralFibreImpliesExactDegree : Set where
data SameRankNullityImpliesSameRecurrenceComplexity : Set where
data ConsumerSurvivalImpliesHistoricalIdentity : Set where

syntheticCoverageDoesNotCreateProductionCoverage : SyntheticCoverageImpliesProductionCoverage → ⊥
syntheticCoverageDoesNotCreateProductionCoverage ()

oneStructuralFibreDoesNotCreateExactDegree : OneStructuralFibreImpliesExactDegree → ⊥
oneStructuralFibreDoesNotCreateExactDegree ()

sameRankNullityDoesNotCreateSameRecurrence : SameRankNullityImpliesSameRecurrenceComplexity → ⊥
sameRankNullityDoesNotCreateSameRecurrence ()

consumerSurvivalDoesNotCreateHistoricalIdentity : ConsumerSurvivalImpliesHistoricalIdentity → ⊥
consumerSurvivalDoesNotCreateHistoricalIdentity ()
