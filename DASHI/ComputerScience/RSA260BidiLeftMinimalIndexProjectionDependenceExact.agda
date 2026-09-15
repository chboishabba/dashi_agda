module DASHI.ComputerScience.RSA260BidiLeftMinimalIndexProjectionDependenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.ComputerScience.RSA260BidiLeftMinimalIndexAsymmetryExact as LeftIndex

------------------------------------------------------------------------
-- RSA-260 BIDI PROJECTION-RELATIVE LEFT MINIMAL-INDEX ASYMMETRY
--
-- The predecessor owner isolated extension orientation as a coordinate missing
-- from the square-Hankel observer.  The next experiment asks whether the
-- observed left-only extension belongs intrinsically to the prepared operator
-- or depends on the projection used to observe its block sequence.
--
-- Reconstructed baseline exceptions:
--   touched=32,  seed=271003, d=22, signature (row,col,square)=(1,0,1)
--   touched=64,  seed=271007, d=29, signature (1,0,1)
--   touched=128, seed=271007, d=44, signature (1,0,1)
--
-- Changing only the X projection gives:
--   32/x3:  d=22, signature (0,0,0)
--   64/x1:  d=31, signature (0,0,0) at the recomputed degree
--   128/x1: d=44, signature (0,0,0)
--
-- Thus the left extension is not an operator-only invariant on these checked
-- carriers.  In two cases the projected generator degree is unchanged while
-- the extension disappears; in one case both the degree and extension change.
------------------------------------------------------------------------

leftIndexBoundary : LeftIndex.LeftMinimalIndexInterpretationBoundary
leftIndexBoundary = LeftIndex.canonicalLeftMinimalIndexInterpretationBoundary

record ProjectionDependenceRuntimeReceipt : Set where
  constructor projection-dependence-runtime-receipt
  field
    subsetRuntimePath : String
    subsetRuntimeGitBlob : String
    subsetRuntimeSHA256 : String
    subsetOutputSHA256 : String
    degreeCheckRuntimePath : String
    degreeCheckRuntimeGitBlob : String
    degreeCheckRuntimeSHA256 : String
    exactLocalRuntimeExecuted : Bool
    runtimeCommittedToProducerRepository : Bool
open ProjectionDependenceRuntimeReceipt public

currentProjectionDependenceRuntimeReceipt : ProjectionDependenceRuntimeReceipt
currentProjectionDependenceRuntimeReceipt = projection-dependence-runtime-receipt
  "/mnt/data/rsa260_left_extension_projection_subset.py"
  "c7731702bd46acf696db5c7050ae02db680d32b7"
  "8c7074bd36ad714a2cb93efeb572abefc0003c3111a95883f41d98965865d982"
  "e39e5e316107978c9df32268c70a387fa4e95d5e46c08d591b836d1430f8b8c2"
  "/mnt/data/rsa260_projection_degree_check.py"
  "d3cb042656da04cc857a6fa18c620d65e9bd91db"
  "c3963c9da32c6b97e9e61df2222b70536d5b0276e25b9165b7fc4d6664d4a36a"
  true
  false

record ProjectionCaseReceipt : Set where
  constructor projection-case-receipt
  field
    touchedRows : Nat
    perturbationSeed : Nat
    baselineProjectionIndex : Nat
    alternateProjectionIndex : Nat
    baselineGeneratorDegree : Nat
    alternateGeneratorDegree : Nat
    baselineRowExtension : Nat
    baselineColumnExtension : Nat
    baselineSquareExtension : Nat
    alternateRowExtension : Nat
    alternateColumnExtension : Nat
    alternateSquareExtension : Nat
open ProjectionCaseReceipt public

case32 : ProjectionCaseReceipt
case32 = projection-case-receipt
  32 271003 0 3
  22 22
  1 0 1
  0 0 0

case64 : ProjectionCaseReceipt
case64 = projection-case-receipt
  64 271007 0 1
  29 31
  1 0 1
  0 0 0

case128 : ProjectionCaseReceipt
case128 = projection-case-receipt
  128 271007 0 1
  44 44
  1 0 1
  0 0 0

record SameCarrierProjectionDependenceReceipt : Set where
  constructor same-carrier-projection-dependence-receipt
  field
    checkedBaselineExceptionCarriers : Nat
    everyCheckedCarrierHasProjectionRemovingLeftExtension : Bool
    carriersWhereDegreeStayedFixedButExtensionChanged : Nat
    carriersWhereDegreeAndExtensionBothChanged : Nat
    leftExtensionIsOperatorOnlyInvariantOnCheckedCases : Bool
    projectionCanChangeExtensionAtFixedGeneratorDegree : Bool
    projectionCanChangeProjectedGeneratorDegree : Bool
open SameCarrierProjectionDependenceReceipt public

currentSameCarrierProjectionDependenceReceipt :
  SameCarrierProjectionDependenceReceipt
currentSameCarrierProjectionDependenceReceipt =
  same-carrier-projection-dependence-receipt
    3
    true
    2
    1
    false
    true
    true

------------------------------------------------------------------------
-- Exact finite obstruction at fixed carrier AND fixed generator degree.
--
-- The 32-row carrier under X-projection 0 and X-projection 3 has the same
-- carrier and the same projected generator degree d=22, yet its rectangular
-- extension answer differs.  Therefore even (carrier,degree) is insufficient
-- for the extension consumer unless the projection coordinate is retained.
------------------------------------------------------------------------

data ProjectionWorld : Set where
  carrier32Projection0 : ProjectionWorld
  carrier32Projection3 : ProjectionWorld

data CarrierDegreeSurface : Set where
  carrier32Degree22 : CarrierDegreeSurface

data ProjectionRefinedSurface : Set where
  carrier32Degree22Projection0 : ProjectionRefinedSurface
  carrier32Degree22Projection3 : ProjectionRefinedSurface

data ExtensionQuery : Set where
  rectangularExtensionQuery : ExtensionQuery

data ExtensionAnswer : Set where
  leftOnlyExtensionAnswer : ExtensionAnswer
  noExtensionAnswer : ExtensionAnswer

carrierDegreeObserve : ProjectionWorld → CarrierDegreeSurface
carrierDegreeObserve _ = carrier32Degree22

projectionRefinedObserve : ProjectionWorld → ProjectionRefinedSurface
projectionRefinedObserve carrier32Projection0 = carrier32Degree22Projection0
projectionRefinedObserve carrier32Projection3 = carrier32Degree22Projection3

extensionAnswer : ExtensionQuery → ProjectionWorld → ExtensionAnswer
extensionAnswer rectangularExtensionQuery carrier32Projection0 = leftOnlyExtensionAnswer
extensionAnswer rectangularExtensionQuery carrier32Projection3 = noExtensionAnswer

extensionSemantics :
  Query.QuerySemantics ProjectionWorld ExtensionQuery ExtensionAnswer
extensionSemantics = Query.querySemantics extensionAnswer

CarrierDegreeExtensionAdequacyDefect : Set₁
CarrierDegreeExtensionAdequacyDefect =
  Query.QueryAdequacyDefect
    carrierDegreeObserve extensionSemantics rectangularExtensionQuery

carrierAndDegreeCannotDetermineProjectionRelativeExtension :
  CarrierDegreeExtensionAdequacyDefect
carrierAndDegreeCannotDetermineProjectionRelativeExtension =
  Query.queryAdequacyDefect
    carrier32Projection0
    carrier32Projection3
    refl
    (λ ())

carrierDegreeExtensionNotAdequate :
  Query.AdequateFor
    carrierDegreeObserve extensionSemantics rectangularExtensionQuery → ⊥
carrierDegreeExtensionNotAdequate =
  Query.queryAdequacyDefectBlocksFactorisation
    carrierAndDegreeCannotDetermineProjectionRelativeExtension

extensionFromProjectionRefined : ProjectionRefinedSurface → ExtensionAnswer
extensionFromProjectionRefined carrier32Degree22Projection0 = leftOnlyExtensionAnswer
extensionFromProjectionRefined carrier32Degree22Projection3 = noExtensionAnswer

projectionRefinedFactorisation :
  (world : ProjectionWorld) →
  extensionAnswer rectangularExtensionQuery world
    ≡ extensionFromProjectionRefined (projectionRefinedObserve world)
projectionRefinedFactorisation carrier32Projection0 = refl
projectionRefinedFactorisation carrier32Projection3 = refl

ProjectionRefinedExtensionAdequacy : Set₁
ProjectionRefinedExtensionAdequacy =
  Query.AdequateFor
    projectionRefinedObserve extensionSemantics rectangularExtensionQuery

extensionFactorsThroughProjectionRefinedObserver :
  ProjectionRefinedExtensionAdequacy
extensionFactorsThroughProjectionRefinedObserver =
  Query.factorsForQuery
    extensionFromProjectionRefined
    projectionRefinedFactorisation

------------------------------------------------------------------------
-- Interpretation boundary.
------------------------------------------------------------------------

record LeftMinimalIndexProjectionBoundary : Set where
  constructor left-minimal-index-projection-boundary
  field
    baselineThreeExceptionsReconstructed : Bool
    alternateXProjectionTestedOnEveryBaselineException : Bool
    everyCheckedExceptionHasProjectionWithNoLeftExtension : Bool
    extensionCanChangeWhileGeneratorDegreeStaysFixed : Bool
    generatorDegreeCanAlsoChangeWithProjection : Bool
    checkedLeftExtensionIsOperatorOnlyInvariant : Bool
    carrierPlusGeneratorDegreeDeterminesExtension : Bool
    carrierPlusDegreeHasConcreteAdequacyDefect : Bool
    addingProjectionCoordinateRepairsFiniteExtensionConsumer : Bool
    projectionDependenceIsUniversalBlockWiedemannTheorem : Bool
    localProjectionExperimentPaysProductionIdentity : Bool
open LeftMinimalIndexProjectionBoundary public

canonicalLeftMinimalIndexProjectionBoundary :
  LeftMinimalIndexProjectionBoundary
canonicalLeftMinimalIndexProjectionBoundary =
  left-minimal-index-projection-boundary
    true
    true
    true
    true
    true
    false
    false
    true
    true
    false
    false

------------------------------------------------------------------------
-- New live residual.
------------------------------------------------------------------------

data LeftMinimalIndexProjectionResidual : Set where
  characterizeProjectionGeometryCreatingLeftExtension : LeftMinimalIndexProjectionResidual
  testIndependentYProjectionFamilies : LeftMinimalIndexProjectionResidual
  freezeProjectionBeforeCrossCarrierComparison : LeftMinimalIndexProjectionResidual
  deriveProjectionIndexedMinimalGeneratorStatement : LeftMinimalIndexProjectionResidual
  liftProjectionIndexedRepairToGeneratorDegreeConsumer : LeftMinimalIndexProjectionResidual
  acquireSameObjectAStarOrFSolsWithProjectionMetadata : LeftMinimalIndexProjectionResidual

firstLeftMinimalIndexProjectionResidual : LeftMinimalIndexProjectionResidual
firstLeftMinimalIndexProjectionResidual =
  characterizeProjectionGeometryCreatingLeftExtension

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data LeftExtensionMeansOperatorInvariant : Set where
data FixedDegreeMeansFixedMinimalIndexSignature : Set where
data ProjectionDependenceMeansArbitraryMeasurementArtifact : Set where
data SyntheticProjectionEffectMeansProductionProjectionIdentity : Set where

leftExtensionDoesNotCreateOperatorInvariant :
  LeftExtensionMeansOperatorInvariant → ⊥
leftExtensionDoesNotCreateOperatorInvariant ()

fixedDegreeDoesNotFixMinimalIndexSignature :
  FixedDegreeMeansFixedMinimalIndexSignature → ⊥
fixedDegreeDoesNotFixMinimalIndexSignature ()

projectionDependenceDoesNotMeanArbitraryArtifact :
  ProjectionDependenceMeansArbitraryMeasurementArtifact → ⊥
projectionDependenceDoesNotMeanArbitraryArtifact ()

syntheticProjectionEffectDoesNotCreateProductionProjectionIdentity :
  SyntheticProjectionEffectMeansProductionProjectionIdentity → ⊥
syntheticProjectionEffectDoesNotCreateProductionProjectionIdentity ()
