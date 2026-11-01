module DASHI.ComputerScience.RSA260BidiLeftMinimalIndexAsymmetryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.ComputerScience.RSA260BidiBlockHankelInvariantFactorOffsetExact as Hankel

------------------------------------------------------------------------
-- RSA-260 BIDI LEFT MINIMAL-INDEX ASYMMETRY REFINEMENT
--
-- The previous owner established an executed rectangular-Hankel signature for
-- all three surviving training exceptions:
--
--   rank H_(d+1,d) - rank H_(d,d) = 1
--   rank H_(d,d+1) - rank H_(d,d) = 0
--
-- while matched non-exceptions have (0,0).  This module isolates the exact
-- information-theoretic content of that result.
--
-- A square extension count alone cannot determine WHICH SIDE supplied an
-- extra rank: left-only and right-only extensions can share the same square
-- extension.  Joining the rectangular row/column coordinates repairs that
-- orientation consumer exactly on the finite model.
--
-- The observed RSA-260 synthetic exceptions instantiate the left-only branch.
-- This does NOT prove a basis-independent or universal block minimal-index
-- theorem, and it does not yet close the original generator-degree consumer.
------------------------------------------------------------------------

hankelBoundary : Hankel.BlockHankelOffsetInterpretationBoundary
hankelBoundary = Hankel.canonicalBlockHankelOffsetInterpretationBoundary

hankelAsymmetryReceipt : Hankel.RectangularHankelAsymmetryReceipt
hankelAsymmetryReceipt = Hankel.currentRectangularHankelAsymmetryReceipt

------------------------------------------------------------------------
-- Finite orientation model.
------------------------------------------------------------------------

data OrientationWorld : Set where
  noRectangularExtension : OrientationWorld
  leftOnlyExtension : OrientationWorld
  rightOnlyExtension : OrientationWorld
  bilateralExtension : OrientationWorld

data SquareExtensionSurface : Set where
  squareExtensionZero : SquareExtensionSurface
  squareExtensionOne : SquareExtensionSurface

data RectangularExtensionSurface : Set where
  rectangularZeroZero : RectangularExtensionSurface
  rectangularOneZero : RectangularExtensionSurface
  rectangularZeroOne : RectangularExtensionSurface
  rectangularOneOne : RectangularExtensionSurface

data OrientationQuery : Set where
  extensionOrientation : OrientationQuery

data OrientationAnswer : Set where
  noExtensionAnswer : OrientationAnswer
  leftExtensionAnswer : OrientationAnswer
  rightExtensionAnswer : OrientationAnswer
  bilateralExtensionAnswer : OrientationAnswer

squareObserve : OrientationWorld → SquareExtensionSurface
squareObserve noRectangularExtension = squareExtensionZero
squareObserve leftOnlyExtension = squareExtensionOne
squareObserve rightOnlyExtension = squareExtensionOne
squareObserve bilateralExtension = squareExtensionOne

rectangularObserve : OrientationWorld → RectangularExtensionSurface
rectangularObserve noRectangularExtension = rectangularZeroZero
rectangularObserve leftOnlyExtension = rectangularOneZero
rectangularObserve rightOnlyExtension = rectangularZeroOne
rectangularObserve bilateralExtension = rectangularOneOne

orientationAnswer : OrientationQuery → OrientationWorld → OrientationAnswer
orientationAnswer extensionOrientation noRectangularExtension = noExtensionAnswer
orientationAnswer extensionOrientation leftOnlyExtension = leftExtensionAnswer
orientationAnswer extensionOrientation rightOnlyExtension = rightExtensionAnswer
orientationAnswer extensionOrientation bilateralExtension = bilateralExtensionAnswer

orientationSemantics :
  Query.QuerySemantics OrientationWorld OrientationQuery OrientationAnswer
orientationSemantics = Query.querySemantics orientationAnswer

------------------------------------------------------------------------
-- Exact obstruction: square extension does not determine orientation.
------------------------------------------------------------------------

SquareExtensionAdequacyDefect : Set₁
SquareExtensionAdequacyDefect =
  Query.QueryAdequacyDefect
    squareObserve orientationSemantics extensionOrientation

squareExtensionCannotDetermineOrientation : SquareExtensionAdequacyDefect
squareExtensionCannotDetermineOrientation =
  Query.queryAdequacyDefect
    leftOnlyExtension
    rightOnlyExtension
    refl
    (λ ())

squareExtensionOrientationNotAdequate :
  Query.AdequateFor squareObserve orientationSemantics extensionOrientation → ⊥
squareExtensionOrientationNotAdequate =
  Query.queryAdequacyDefectBlocksFactorisation
    squareExtensionCannotDetermineOrientation

------------------------------------------------------------------------
-- Constructive repair: retain row/column orientation.
------------------------------------------------------------------------

orientationFromRectangular : RectangularExtensionSurface → OrientationAnswer
orientationFromRectangular rectangularZeroZero = noExtensionAnswer
orientationFromRectangular rectangularOneZero = leftExtensionAnswer
orientationFromRectangular rectangularZeroOne = rightExtensionAnswer
orientationFromRectangular rectangularOneOne = bilateralExtensionAnswer

orientationFactorisation :
  (world : OrientationWorld) →
  orientationAnswer extensionOrientation world
    ≡ orientationFromRectangular (rectangularObserve world)
orientationFactorisation noRectangularExtension = refl
orientationFactorisation leftOnlyExtension = refl
orientationFactorisation rightOnlyExtension = refl
orientationFactorisation bilateralExtension = refl

RefinedOrientationAdequacy : Set₁
RefinedOrientationAdequacy =
  Query.AdequateFor rectangularObserve orientationSemantics extensionOrientation

orientationFactorsThroughRefinedObserver : RefinedOrientationAdequacy
orientationFactorsThroughRefinedObserver =
  Query.factorsForQuery orientationFromRectangular orientationFactorisation

------------------------------------------------------------------------
-- Executed observation -> typed left-asymmetry statement.
------------------------------------------------------------------------

record LeftMinimalIndexAsymmetryStatement : Set where
  constructor left-minimal-index-asymmetry-statement
  field
    checkedExceptionWitnesses : Nat
    checkedMatchedNonExceptionWitnesses : Nat
    exceptionRowExtension : Nat
    exceptionColumnExtension : Nat
    exceptionSquareExtension : Nat
    matchedRowExtension : Nat
    matchedColumnExtension : Nat
    matchedSquareExtension : Nat
    observedExceptionOrientationIsLeftOnly : Bool
    statementIsUniversalMinimalIndexTheorem : Bool
open LeftMinimalIndexAsymmetryStatement public

currentLeftMinimalIndexAsymmetryStatement : LeftMinimalIndexAsymmetryStatement
currentLeftMinimalIndexAsymmetryStatement =
  left-minimal-index-asymmetry-statement
    3 6
    1 0 1
    0 0 0
    true
    false

------------------------------------------------------------------------
-- Status boundary: distinguish the repaired orientation consumer from the
-- still-open original generator-degree consumer.
------------------------------------------------------------------------

record LeftMinimalIndexInterpretationBoundary : Set where
  constructor left-minimal-index-interpretation-boundary
  field
    rectangularHankelExecutionReceiptInherited : Bool
    allThreeObservedExceptionsAreLeftOnlyOnCheckedProbe : Bool
    matchedNonExceptionsAreZeroZeroOnCheckedProbe : Bool
    squareExtensionAloneDeterminesOrientation : Bool
    squareExtensionHasConcreteOrientationAdequacyDefect : Bool
    rectangularObserverStrictlyAddsOrientationCoordinate : Bool
    orientationConsumerFactorsThroughRectangularObserver : Bool
    leftOnlyObservationIsUniversalMinimalIndexTheorem : Bool
    orientationRepairClosesOriginalGeneratorDegreeConsumer : Bool
    orientationRepairPaysProductionSameObjectIdentity : Bool
    orientationRepairPaysHistoricalMatrixCustody : Bool
open LeftMinimalIndexInterpretationBoundary public

canonicalLeftMinimalIndexInterpretationBoundary :
  LeftMinimalIndexInterpretationBoundary
canonicalLeftMinimalIndexInterpretationBoundary =
  left-minimal-index-interpretation-boundary
    true
    true
    true
    false
    true
    true
    true
    false
    false
    false
    false

------------------------------------------------------------------------
-- The live residual is now causal/structural rather than merely descriptive.
------------------------------------------------------------------------

data LeftMinimalIndexResidual : Set where
  explainWhyThreeTrainingProjectionsCarryLeftExtension : LeftMinimalIndexResidual
  testLeftExtensionAcrossIndependentProjectionFamilies : LeftMinimalIndexResidual
  deriveBasisIndependentMinimalIndexStatement : LeftMinimalIndexResidual
  liftOrientationRepairToGeneratorDegreeConsumer : LeftMinimalIndexResidual
  acquireSameObjectAStarOrFSolsForProductionRectangularHankel : LeftMinimalIndexResidual

firstLeftMinimalIndexResidual : LeftMinimalIndexResidual
firstLeftMinimalIndexResidual =
  explainWhyThreeTrainingProjectionsCarryLeftExtension

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data SquareRankExtensionMeansLeftExtension : Set where
data CheckedLeftExtensionMeansUniversalMinimalIndex : Set where
data OrientationAdequacyMeansGeneratorDegreeAdequacy : Set where
data SyntheticRectangularHankelMeansProductionIdentity : Set where

squareRankExtensionDoesNotChooseSide :
  SquareRankExtensionMeansLeftExtension → ⊥
squareRankExtensionDoesNotChooseSide ()

checkedLeftExtensionDoesNotCreateUniversalMinimalIndex :
  CheckedLeftExtensionMeansUniversalMinimalIndex → ⊥
checkedLeftExtensionDoesNotCreateUniversalMinimalIndex ()

orientationAdequacyDoesNotCreateGeneratorDegreeAdequacy :
  OrientationAdequacyMeansGeneratorDegreeAdequacy → ⊥
orientationAdequacyDoesNotCreateGeneratorDegreeAdequacy ()

syntheticRectangularHankelDoesNotCreateProductionIdentity :
  SyntheticRectangularHankelMeansProductionIdentity → ⊥
syntheticRectangularHankelDoesNotCreateProductionIdentity ()
