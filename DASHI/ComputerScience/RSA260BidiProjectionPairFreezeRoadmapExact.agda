module DASHI.ComputerScience.RSA260BidiProjectionPairFreezeRoadmapExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.ComputerScience.RSA260BidiLeftMinimalIndexProjectionDependenceExact as XProjection
import DASHI.ComputerScience.RSA260ProductionSubstitutionRoadmapExact as PriorRoadmap

------------------------------------------------------------------------
-- RSA-260 BIDI PROJECTION-PAIR FREEZE / PRODUCTION ROADMAP REFINEMENT
--
-- X-projection variation already showed that rectangular-Hankel minimal-index
-- signatures are projection-relative.  The follow-up fixes X and changes only
-- Y on the three baseline exception carriers, at their previously paid degree.
--
-- Observed fixed-degree signatures (row,col,square):
--
--   32, d=22:  Y0=(1,0,1), Y1=(0,0,1), Y3=(0,0,0)
--   64, d=29:  Y0=(1,0,1), Y1=(1,1,2), Y3=(1,0,1)
--  128, d=44:  Y0=(1,0,1), Y1=(0,1,1), Y3=(1,0,1)
--
-- Therefore the diagnostic object is not merely "the operator" or even
-- "operator + generator degree + X projection".  The projection pair (X,Y)
-- must be retained/frozen for projection-relative Hankel comparisons.
--
-- This does not say every A* artifact lacking projection metadata is useless:
-- it can still carry same-object dynamic sequence information.  It says such
-- an artifact cannot by itself pay projection-relative minimal-index identity
-- or cross-carrier comparability.
------------------------------------------------------------------------

xProjectionBoundary : XProjection.LeftMinimalIndexProjectionBoundary
xProjectionBoundary = XProjection.canonicalLeftMinimalIndexProjectionBoundary

priorRoadmapBoundary : PriorRoadmap.RSA260ProductionSubstitutionBoundary
priorRoadmapBoundary = PriorRoadmap.currentRSA260ProductionSubstitutionBoundary

priorProductionResidual : PriorRoadmap.ProductionResidual
priorProductionResidual = PriorRoadmap.firstUnpaidProductionResidual

priorHighAlphaTarget : PriorRoadmap.ProductionDiagnosticTarget
priorHighAlphaTarget = PriorRoadmap.firstHighAlphaProductionDiagnosticTarget

record YProjectionRuntimeReceipt : Set where
  constructor y-projection-runtime-receipt
  field
    runtimePath : String
    runtimeGitBlob : String
    runtimeSHA256 : String
    outputSHA256 : String
    checkedCarriers : Nat
    yProjectionsPerCarrier : Nat
    referenceDegreeHeldFixedDuringProbe : Bool
    generatorDegreeRecomputedForEveryYProjection : Bool
    exactLocalRuntimeExecuted : Bool
    runtimeCommittedToProducerRepository : Bool
open YProjectionRuntimeReceipt public

currentYProjectionRuntimeReceipt : YProjectionRuntimeReceipt
currentYProjectionRuntimeReceipt = y-projection-runtime-receipt
  "/mnt/data/rsa260_y_projection_rect_subset.py"
  "083bc7b7f2a833fa8974088cd5315267bf4fb1c3"
  "ffb5fc95bdd0dc794a1de38a22a5dd709790778336cdfff2f79f27f47429b1b8"
  "4fca1547928a4b9bbebe8f758828df85f94ac9bb5d7b637b580b6e7385dd11c7"
  3 3 true false true false

record YProjectionCaseReceipt : Set where
  constructor y-projection-case-receipt
  field
    touchedRows : Nat
    referenceDegree : Nat
    yProjection : Nat
    rankDD : Nat
    rowExtension : Nat
    columnExtension : Nat
    squareExtension : Nat
open YProjectionCaseReceipt public

case128Y0 : YProjectionCaseReceipt
case128Y0 = y-projection-case-receipt 128 44 0 351 1 0 1

case128Y1 : YProjectionCaseReceipt
case128Y1 = y-projection-case-receipt 128 44 1 349 0 1 1

case64Y1 : YProjectionCaseReceipt
case64Y1 = y-projection-case-receipt 64 29 1 230 1 1 2

case32Y3 : YProjectionCaseReceipt
case32Y3 = y-projection-case-receipt 32 22 3 173 0 0 0

------------------------------------------------------------------------
-- Exact finite obstruction: same carrier, same d, same X; changing Y changes
-- extension orientation.  Hence Y must be retained for this consumer.
------------------------------------------------------------------------

data YProjectionWorld : Set where
  carrier128X0Y0 : YProjectionWorld
  carrier128X0Y1 : YProjectionWorld

data CarrierDegreeXSurface : Set where
  carrier128Degree44X0 : CarrierDegreeXSurface

data ProjectionPairSurface : Set where
  carrier128Degree44X0Y0 : ProjectionPairSurface
  carrier128Degree44X0Y1 : ProjectionPairSurface

data PairQuery : Set where
  rectangularOrientationQuery : PairQuery

data PairAnswer : Set where
  leftOnlyAnswer : PairAnswer
  rightOnlyAnswer : PairAnswer

carrierDegreeXObserve : YProjectionWorld → CarrierDegreeXSurface
carrierDegreeXObserve _ = carrier128Degree44X0

projectionPairObserve : YProjectionWorld → ProjectionPairSurface
projectionPairObserve carrier128X0Y0 = carrier128Degree44X0Y0
projectionPairObserve carrier128X0Y1 = carrier128Degree44X0Y1

pairAnswer : PairQuery → YProjectionWorld → PairAnswer
pairAnswer rectangularOrientationQuery carrier128X0Y0 = leftOnlyAnswer
pairAnswer rectangularOrientationQuery carrier128X0Y1 = rightOnlyAnswer

pairSemantics : Query.QuerySemantics YProjectionWorld PairQuery PairAnswer
pairSemantics = Query.querySemantics pairAnswer

MissingYProjectionAdequacyDefect : Set₁
MissingYProjectionAdequacyDefect =
  Query.QueryAdequacyDefect
    carrierDegreeXObserve pairSemantics rectangularOrientationQuery

sameCarrierDegreeXCannotDetermineOrientationWithoutY :
  MissingYProjectionAdequacyDefect
sameCarrierDegreeXCannotDetermineOrientationWithoutY =
  Query.queryAdequacyDefect
    carrier128X0Y0
    carrier128X0Y1
    refl
    (λ ())

carrierDegreeXNotAdequateWithoutY :
  Query.AdequateFor
    carrierDegreeXObserve pairSemantics rectangularOrientationQuery → ⊥
carrierDegreeXNotAdequateWithoutY =
  Query.queryAdequacyDefectBlocksFactorisation
    sameCarrierDegreeXCannotDetermineOrientationWithoutY

answerFromProjectionPair : ProjectionPairSurface → PairAnswer
answerFromProjectionPair carrier128Degree44X0Y0 = leftOnlyAnswer
answerFromProjectionPair carrier128Degree44X0Y1 = rightOnlyAnswer

pairFactorisation :
  (world : YProjectionWorld) →
  pairAnswer rectangularOrientationQuery world
    ≡ answerFromProjectionPair (projectionPairObserve world)
pairFactorisation carrier128X0Y0 = refl
pairFactorisation carrier128X0Y1 = refl

projectionPairAdequate :
  Query.AdequateFor
    projectionPairObserve pairSemantics rectangularOrientationQuery
projectionPairAdequate =
  Query.factorsForQuery answerFromProjectionPair pairFactorisation

------------------------------------------------------------------------
-- Roadmap recut: preserve the older acquisition order, but refine the dynamic
-- diagnostic target with projection-pair custody/freeze requirements.
------------------------------------------------------------------------

data RefinedProductionDiagnosticTarget : Set where
  sameObjectSparseMatrixForDirectIncidence : RefinedProductionDiagnosticTarget
  sameObjectBalancingForPreparationGeometry : RefinedProductionDiagnosticTarget
  sameObjectKrylovAForDynamicSpan : RefinedProductionDiagnosticTarget
  sameObjectKrylovAWithProjectionPairMetadata : RefinedProductionDiagnosticTarget
  sameObjectGeneratorFForRealizedRecurrence : RefinedProductionDiagnosticTarget

firstRefinedHighAlphaProductionDiagnosticTarget :
  RefinedProductionDiagnosticTarget
firstRefinedHighAlphaProductionDiagnosticTarget =
  sameObjectKrylovAWithProjectionPairMetadata

data ProjectionPairRoadmapResidual : Set where
  recoverOrBindXProjectionIdentity : ProjectionPairRoadmapResidual
  recoverOrBindYProjectionIdentity : ProjectionPairRoadmapResidual
  freezeProjectionPairBeforeCrossCarrierComparison : ProjectionPairRoadmapResidual
  recomputeGeneratorDegreeAcrossYProjectionFamily : ProjectionPairRoadmapResidual
  deriveProjectionIndexedMinimalGeneratorStatement : ProjectionPairRoadmapResidual
  liftProjectionIndexedHankelRepairToDegreeConsumer : ProjectionPairRoadmapResidual
  acquireSameObjectAStarOrFSolsWithProjectionPairMetadata : ProjectionPairRoadmapResidual

firstProjectionPairRoadmapResidual : ProjectionPairRoadmapResidual
firstProjectionPairRoadmapResidual =
  recomputeGeneratorDegreeAcrossYProjectionFamily

record ProjectionPairRoadmapBoundary : Set where
  constructor projection-pair-roadmap-boundary
  field
    xProjectionDependencePaid : Bool
    yProjectionDependencePaidAtFixedReferenceDegree : Bool
    yProjectionCanFlipLeftOnlyToRightOnly : Bool
    yProjectionCanCreateBilateralExtension : Bool
    yProjectionCanRemoveExtension : Bool
    projectionPairRequiredForMinimalIndexComparison : Bool
    projectionPairAlreadyProvedRequiredForAllConsumers : Bool
    projectionPairMustBeFrozenBeforeCrossCarrierHankelComparison : Bool
    sameObjectAStarStillHighAlphaDynamicArtifact : Bool
    AStarWithoutProjectionMetadataPaysDynamicSequenceIdentity : Bool
    AStarWithoutProjectionMetadataPaysProjectionRelativeMinimalIndexIdentity : Bool
    projectionMetadataPaysMatrixCustody : Bool
    productionAcquisitionResidualStillRequiresSameObjectArtifact : Bool
    productionMatrixBytesAlreadyPaid : Bool
    yProjectionGeneratorDegreeRecomputationPaid : Bool
open ProjectionPairRoadmapBoundary public

canonicalProjectionPairRoadmapBoundary : ProjectionPairRoadmapBoundary
canonicalProjectionPairRoadmapBoundary =
  projection-pair-roadmap-boundary
    true
    true
    true
    true
    true
    true
    false
    true
    true
    true
    false
    false
    true
    false
    false

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data AStarWithoutProjectionMeansMinimalIndexIdentity : Set where
data ProjectionMetadataMeansMatrixCustody : Set where
data FixedReferenceDegreeProbeMeansRecomputedGeneratorDegree : Set where
data ProjectionPairNeededForOneConsumerMeansNeededForAllConsumers : Set where

astarWithoutProjectionDoesNotCreateMinimalIndexIdentity :
  AStarWithoutProjectionMeansMinimalIndexIdentity → ⊥
astarWithoutProjectionDoesNotCreateMinimalIndexIdentity ()

projectionMetadataDoesNotCreateMatrixCustody :
  ProjectionMetadataMeansMatrixCustody → ⊥
projectionMetadataDoesNotCreateMatrixCustody ()

fixedDegreeProbeDoesNotMeanDegreeRecomputed :
  FixedReferenceDegreeProbeMeansRecomputedGeneratorDegree → ⊥
fixedDegreeProbeDoesNotMeanDegreeRecomputed ()

consumerSpecificNeedDoesNotBecomeUniversalNeed :
  ProjectionPairNeededForOneConsumerMeansNeededForAllConsumers → ⊥
consumerSpecificNeedDoesNotBecomeUniversalNeed ()
