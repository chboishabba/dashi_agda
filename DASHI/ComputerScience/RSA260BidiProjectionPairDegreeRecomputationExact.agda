module DASHI.ComputerScience.RSA260BidiProjectionPairDegreeRecomputationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.ComputerScience.RSA260BidiProjectionPairFreezeRoadmapExact as PairRoadmap

------------------------------------------------------------------------
-- RSA-260 BIDI PROJECTION-PAIR DEGREE RECOMPUTATION
--
-- The fixed-reference-degree Y sweep showed that Y can change rectangular
-- Hankel orientation.  We now recompute the projected shared-generator degree
-- using the same held-out-valid recurrence solver on selected alternate Y
-- projections.
--
-- Results:
--   32 / Y1 : 22 -> 23
--   32 / Y3 : 22 -> 22
--   64 / Y1 : 29 -> 30
--  128 / Y1 : 44 -> 45
--  128 / Y3 : 44 -> 44
--
-- Thus projection can change recurrence scale, but need not.  Combined with
-- the prior Hankel sweep, degree and extension orientation are distinct
-- projection-relative coordinates: at 32/Y3 degree stays 22 while the prior
-- left-only extension disappears.
--
-- Roadmap consequence: an authentic projected A* sequence can pay realized
-- degree/Hankel diagnostics for THAT sequence even if X/Y vectors are absent.
-- X/Y projection custody is additionally required for projection reproduction,
-- projection-geometry explanation, and controlled cross-sequence comparison.
------------------------------------------------------------------------

pairRoadmapBoundary : PairRoadmap.ProjectionPairRoadmapBoundary
pairRoadmapBoundary = PairRoadmap.canonicalProjectionPairRoadmapBoundary

record ProjectionDegreeRuntimeReceipt : Set where
  constructor projection-degree-runtime-receipt
  field
    singleCaseRuntimePath : String
    singleCaseRuntimeGitBlob : String
    singleCaseRuntimeSHA256 : String
    batchRuntimePath : String
    batchRuntimeGitBlob : String
    batchRuntimeSHA256 : String
    batchOutputSHA256 : String
    recomputedCases : Nat
    exactLocalRuntimeExecuted : Bool
    runtimeCommittedToProducerRepository : Bool
open ProjectionDegreeRuntimeReceipt public

currentProjectionDegreeRuntimeReceipt : ProjectionDegreeRuntimeReceipt
currentProjectionDegreeRuntimeReceipt = projection-degree-runtime-receipt
  "/mnt/data/rsa260_y_projection_degree_one.py"
  "0999a971a88fd4cfc4f702af213114e7ce667fe6"
  "204fe389172961610a406747479439940c83b9220b0c010fadc3f16fb76acecf"
  "/mnt/data/rsa260_y_projection_degree_batch.py"
  "c26ebb7d567f368b7ac749c4b41c517044d86f75"
  "93bb265783a085b82bc022707d70835e9adfb16d246dca5a95e72048a119c95e"
  "8d089d4fa7bd5057908d7c15a022ba4f724cc1390419189ad40c6059c105c125"
  5 true false

record ProjectionDegreeCase : Set where
  constructor projection-degree-case
  field
    touchedRows : Nat
    perturbationSeed : Nat
    yProjection : Nat
    baselineDegree : Nat
    recomputedDegree : Nat
open ProjectionDegreeCase public

case32Y1 : ProjectionDegreeCase
case32Y1 = projection-degree-case 32 271003 1 22 23

case32Y3 : ProjectionDegreeCase
case32Y3 = projection-degree-case 32 271003 3 22 22

case64Y1 : ProjectionDegreeCase
case64Y1 = projection-degree-case 64 271007 1 29 30

case128Y1 : ProjectionDegreeCase
case128Y1 = projection-degree-case 128 271007 1 44 45

case128Y3 : ProjectionDegreeCase
case128Y3 = projection-degree-case 128 271007 3 44 44

record ProjectionDegreePortfolioReceipt : Set where
  constructor projection-degree-portfolio-receipt
  field
    checkedCases : Nat
    casesWhereYChangedDegree : Nat
    casesWhereYPreservedDegree : Nat
    maximumObservedDegreeShift : Nat
    projectionCanChangeProjectedDegree : Bool
    projectionNeedNotChangeProjectedDegree : Bool
    degreeAloneDeterminesRectangularExtension : Bool
open ProjectionDegreePortfolioReceipt public

currentProjectionDegreePortfolioReceipt : ProjectionDegreePortfolioReceipt
currentProjectionDegreePortfolioReceipt =
  projection-degree-portfolio-receipt
    5 3 2 1 true true false

------------------------------------------------------------------------
-- Exact finite obstruction: same carrier and fixed X can produce different
-- projected generator degree under different Y projections.
------------------------------------------------------------------------

data DegreeWorld : Set where
  carrier128X0Y0 : DegreeWorld
  carrier128X0Y1 : DegreeWorld

data CarrierXSurface : Set where
  carrier128X0 : CarrierXSurface

data ProjectionPairSurface : Set where
  carrier128X0Y0Surface : ProjectionPairSurface
  carrier128X0Y1Surface : ProjectionPairSurface

data DegreeQuery : Set where
  projectedGeneratorDegree : DegreeQuery

data DegreeAnswer : Set where
  degree44 : DegreeAnswer
  degree45 : DegreeAnswer

carrierXObserve : DegreeWorld → CarrierXSurface
carrierXObserve _ = carrier128X0

projectionPairObserve : DegreeWorld → ProjectionPairSurface
projectionPairObserve carrier128X0Y0 = carrier128X0Y0Surface
projectionPairObserve carrier128X0Y1 = carrier128X0Y1Surface

degreeAnswer : DegreeQuery → DegreeWorld → DegreeAnswer
degreeAnswer projectedGeneratorDegree carrier128X0Y0 = degree44
degreeAnswer projectedGeneratorDegree carrier128X0Y1 = degree45

degreeSemantics : Query.QuerySemantics DegreeWorld DegreeQuery DegreeAnswer
degreeSemantics = Query.querySemantics degreeAnswer

CarrierXDegreeAdequacyDefect : Set₁
CarrierXDegreeAdequacyDefect =
  Query.QueryAdequacyDefect carrierXObserve degreeSemantics projectedGeneratorDegree

carrierAndXCannotDetermineProjectedGeneratorDegree :
  CarrierXDegreeAdequacyDefect
carrierAndXCannotDetermineProjectedGeneratorDegree =
  Query.queryAdequacyDefect
    carrier128X0Y0
    carrier128X0Y1
    refl
    (λ ())

carrierXDegreeNotAdequate :
  Query.AdequateFor carrierXObserve degreeSemantics projectedGeneratorDegree → ⊥
carrierXDegreeNotAdequate =
  Query.queryAdequacyDefectBlocksFactorisation
    carrierAndXCannotDetermineProjectedGeneratorDegree

degreeFromProjectionPair : ProjectionPairSurface → DegreeAnswer
degreeFromProjectionPair carrier128X0Y0Surface = degree44
degreeFromProjectionPair carrier128X0Y1Surface = degree45

projectionPairDegreeFactorisation :
  (world : DegreeWorld) →
  degreeAnswer projectedGeneratorDegree world
    ≡ degreeFromProjectionPair (projectionPairObserve world)
projectionPairDegreeFactorisation carrier128X0Y0 = refl
projectionPairDegreeFactorisation carrier128X0Y1 = refl

projectionPairAdequateForDegree :
  Query.AdequateFor projectionPairObserve degreeSemantics projectedGeneratorDegree
projectionPairAdequateForDegree =
  Query.factorsForQuery degreeFromProjectionPair projectionPairDegreeFactorisation

------------------------------------------------------------------------
-- Acquisition / roadmap distinction.
------------------------------------------------------------------------

data ProjectedSequenceArtifactCapability : Set where
  measureRealizedProjectedDegree : ProjectedSequenceArtifactCapability
  measureRealizedProjectedHankelProfile : ProjectedSequenceArtifactCapability
  reproduceOriginalProjection : ProjectedSequenceArtifactCapability
  explainProjectionGeometry : ProjectedSequenceArtifactCapability
  compareAcrossProjectionPairsAsControlledExperiment : ProjectedSequenceArtifactCapability

data ProjectionMetadataState : Set where
  sequenceOnly : ProjectionMetadataState
  sequenceWithFrozenProjectionPair : ProjectionMetadataState

capabilityPaid : ProjectionMetadataState → ProjectedSequenceArtifactCapability → Bool
capabilityPaid sequenceOnly measureRealizedProjectedDegree = true
capabilityPaid sequenceOnly measureRealizedProjectedHankelProfile = true
capabilityPaid sequenceOnly reproduceOriginalProjection = false
capabilityPaid sequenceOnly explainProjectionGeometry = false
capabilityPaid sequenceOnly compareAcrossProjectionPairsAsControlledExperiment = false
capabilityPaid sequenceWithFrozenProjectionPair _ = true

record ProjectionAwareAcquisitionBoundary : Set where
  constructor projection-aware-acquisition-boundary
  field
    authenticProjectedAStarCanPayDegreeWithoutXYVectors : Bool
    authenticProjectedAStarCanPayHankelWithoutXYVectors : Bool
    sequenceBytesAlonePayProjectionReproduction : Bool
    sequenceBytesAlonePayProjectionGeometryExplanation : Bool
    controlledCrossProjectionComparisonRequiresProjectionIdentity : Bool
    projectionPairCanChangeDegree : Bool
    projectionPairCanChangeExtensionOrientation : Bool
    degreeAndExtensionOrientationAreSameCoordinate : Bool
    sameObjectAcquisitionStillDominatesSyntheticRefinement : Bool
    matrixFirstIsRequiredBeforeAnyDynamicDiagnostic : Bool
open ProjectionAwareAcquisitionBoundary public

canonicalProjectionAwareAcquisitionBoundary : ProjectionAwareAcquisitionBoundary
canonicalProjectionAwareAcquisitionBoundary =
  projection-aware-acquisition-boundary
    true
    true
    false
    false
    true
    true
    true
    false
    true
    false

------------------------------------------------------------------------
-- Revised Pareto frontier after Y-degree recomputation.
------------------------------------------------------------------------

data ProjectionDegreeRoadmapResidual : Set where
  freezeProjectionPairBeforeCrossCarrierComparison : ProjectionDegreeRoadmapResidual
  characterizeProjectionGeometryCreatingDegreeShift : ProjectionDegreeRoadmapResidual
  characterizeProjectionGeometryCreatingOrientationShift : ProjectionDegreeRoadmapResidual
  deriveProjectionIndexedMinimalGeneratorStatement : ProjectionDegreeRoadmapResidual
  liftProjectionIndexedDiagnosticsToProductionAStar : ProjectionDegreeRoadmapResidual
  acquireSameObjectProjectedAStarOrFSols : ProjectionDegreeRoadmapResidual
  recoverProjectionPairForReproductionAndControlledComparison : ProjectionDegreeRoadmapResidual

firstProjectionDegreeRoadmapResidual : ProjectionDegreeRoadmapResidual
firstProjectionDegreeRoadmapResidual =
  freezeProjectionPairBeforeCrossCarrierComparison

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data AStarSequenceNeedsXYToMeasureItsOwnDegree : Set where
data SameDegreeMeansSameHankelOrientation : Set where
data ProjectionDegreeShiftMeansOperatorChanged : Set where
data ProjectionPairCustodyMeansMatrixCustody : Set where

astarSequenceDoesNotNeedXYForOwnDegree :
  AStarSequenceNeedsXYToMeasureItsOwnDegree → ⊥
astarSequenceDoesNotNeedXYForOwnDegree ()

sameDegreeDoesNotFixHankelOrientation : SameDegreeMeansSameHankelOrientation → ⊥
sameDegreeDoesNotFixHankelOrientation ()

projectionDegreeShiftDoesNotMeanOperatorChanged :
  ProjectionDegreeShiftMeansOperatorChanged → ⊥
projectionDegreeShiftDoesNotMeanOperatorChanged ()

projectionPairCustodyDoesNotCreateMatrixCustody :
  ProjectionPairCustodyMeansMatrixCustody → ⊥
projectionPairCustodyDoesNotCreateMatrixCustody ()
