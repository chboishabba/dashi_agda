module DASHI.Core.RelationalCoordinatePlusOneCrossPollinationExact where

------------------------------------------------------------------------
-- RELATIONAL COORDINATE / +1 CROSS-POLLINATION
--
-- Existing repo constructions contain several exact "+1" shapes:
--
--   9 + 1 = 10
--     exceptional observer / completion marker;
--
--   10 + 1 = 11
--     cross-scale carried bundle plus one fresh local unit;
--
--   53 + 1 = 54
--     restoration of the secondary invariant line;
--
--   196883 + 1 = 196884
--     restoration of the weight-two conformal/vacuum line.
--
-- Nongin 1.1, TSFV history fibres and twistronics registration are NOT
-- identified with those arithmetic units.  They share only the more abstract
-- possibility that retaining one additional distinction/coordinate can make a
-- coarse quotient insufficient for a declared consumer.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.String using (String)

import DASHI.Foundations.ObserverExtensionBoundary as Observer
import DASHI.Foundations.StageValuationBundleAtlas as Stage
import DASHI.Foundations.JPlusOneScaleBridge as JPlusOne
import DASHI.Moonshine.Base369MonsterTwoComponentCompletionBidiExact as MonsterPlusOne
import DASHI.Core.NonginOnePointOneArmyRefinementExact as Nongin
import DASHI.Physics.Closure.TSFVHistoryConditionedChoiceBridgeExact as TSFV
import DASHI.Moonshine.TwistronicsRelativeRegistrationComparatorExact as Twist
import DASHI.Core.ConsumerGuidedReopenableRefinementExact as Refine
import DASHI.Core.IntersectionalNonFactorability as NonFactor
import DASHI.Physics.Closure.TSFVBidirectionalCausticBridgeExact as TSFVCaustic

------------------------------------------------------------------------
-- 1. Exact arithmetic owners reused, not duplicated.
------------------------------------------------------------------------

ninePlusOneIsTen : 9 + 1 ≡ 10
ninePlusOneIsTen = Observer.exceptionalObserverCount

tenPlusOneIsEleven :
  Stage.Stage11CrossScaleJoin.carriedBundleValue Stage.canonicalStage11CrossScaleJoin
  + Stage.Stage11CrossScaleJoin.freshLocalValue Stage.canonicalStage11CrossScaleJoin
  ≡ Stage.Stage11CrossScaleJoin.joinedValue Stage.canonicalStage11CrossScaleJoin
tenPlusOneIsEleven =
  Stage.Stage11CrossScaleJoin.joinIsEleven Stage.canonicalStage11CrossScaleJoin

fiftyThreePlusOneIsFiftyFour : 53 + 1 ≡ 54
fiftyThreePlusOneIsFiftyFour = refl

monsterPlusOneIsMoonshine : 196883 + 1 ≡ 196884
monsterPlusOneIsMoonshine = JPlusOne.moonshineCoefficientIsRepresentationPlusOne

------------------------------------------------------------------------
-- 2. Typed role separation.
------------------------------------------------------------------------

data PlusOneRole : Set where
  exceptionalObserverMarker : PlusOneRole
  crossScaleFreshLocalUnit : PlusOneRole
  secondaryInvariantLine : PlusOneRole
  weightTwoConformalLine : PlusOneRole
  nonginFrameCoordinate : PlusOneRole
  tsfvHistoryResidualCoordinate : PlusOneRole
  twistronicsRegistrationCoordinate : PlusOneRole

exceptionalNotFreshLocal :
  exceptionalObserverMarker ≡ crossScaleFreshLocalUnit -> ⊥
exceptionalNotFreshLocal ()

secondaryInvariantNotConformal :
  secondaryInvariantLine ≡ weightTwoConformalLine -> ⊥
secondaryInvariantNotConformal ()

nonginFrameNotTwist :
  nonginFrameCoordinate ≡ twistronicsRegistrationCoordinate -> ⊥
nonginFrameNotTwist ()

tsfvHistoryNotTwist :
  tsfvHistoryResidualCoordinate ≡ twistronicsRegistrationCoordinate -> ⊥
tsfvHistoryNotTwist ()

------------------------------------------------------------------------
-- 3. Reuse the exact one-plus shapes already present in the Monster lane.
------------------------------------------------------------------------

nineToTenShape : MonsterPlusOne.OnePlusShape
nineToTenShape = MonsterPlusOne.coarseNineToTenShape

fiftyThreeToFiftyFourShape : MonsterPlusOne.OnePlusShape
fiftyThreeToFiftyFourShape =
  MonsterPlusOne.secondaryFiftyThreeToFiftyFourShape

monsterToMoonshineShape : MonsterPlusOne.OnePlusShape
monsterToMoonshineShape =
  MonsterPlusOne.weightTwoMonsterToMoonshineShape

tenToElevenFreshUnit : JPlusOne.FreshUnitExtension
tenToElevenFreshUnit = JPlusOne.stage11FreshUnitExtension

------------------------------------------------------------------------
-- 4. Consumer-sensitive extension instances.
--
-- These are not cardinal +1 claims.  They are strict/non-factorable
-- refinement witnesses showing that a retained distinction can matter.
------------------------------------------------------------------------

nonginRefinement :
  Refine.ConsumerGuidedRefinement
    (Nongin.onePointZeroProject {Nongin.Base1} {Nongin.Frame2})
    (Nongin.onePointOneProject {Nongin.Base1} {Nongin.Frame2})
    Nongin.frameSensitiveResponse
nonginRefinement = Nongin.canonicalOnePointOneRefinement

tsfvCoarseObservationCannotServeHistorySensitiveChoice :
  NonFactor.FactorsThrough
    TSFVCaustic.historyProjection
    TSFV.historySensitiveChoice -> ⊥
tsfvCoarseObservationCannotServeHistorySensitiveChoice =
  TSFV.causticProjectionInsufficientForHistorySensitiveChoice

------------------------------------------------------------------------
-- 5. Shared interpretation boundary.
------------------------------------------------------------------------

record RelationalCoordinatePlusOneBoundary : Set where
  constructor relational-coordinate-plus-one-boundary
  field
    exactNinePlusOneReused : Bool
    exactTenPlusOneReused : Bool
    exactFiftyThreePlusOneReused : Bool
    exactMonsterPlusOneReused : Bool

    arithmeticPlusOneRolesAreIdentical : Bool
    arithmeticPlusOneRolesAreIdenticalIsFalse :
      arithmeticPlusOneRolesAreIdentical ≡ false

    nonginOnePointOneIsLiteralCardinalPlusOne : Bool
    nonginOnePointOneIsLiteralCardinalPlusOneIsFalse :
      nonginOnePointOneIsLiteralCardinalPlusOne ≡ false

    tsfvHistoryResidualIsLiteralCardinalPlusOne : Bool
    tsfvHistoryResidualIsLiteralCardinalPlusOneIsFalse :
      tsfvHistoryResidualIsLiteralCardinalPlusOne ≡ false

    twistAngleIsLiteralCardinalPlusOne : Bool
    twistAngleIsLiteralCardinalPlusOneIsFalse :
      twistAngleIsLiteralCardinalPlusOne ≡ false

    sharedExtensionShapeCanMotivateComparator : Bool
    consumerRelevanceRequiresDistinguishingWitness : Bool
    sameShapeImpliesSameMechanism : Bool
    sameShapeImpliesSameMechanismIsFalse :
      sameShapeImpliesSameMechanism ≡ false

    interpretation : String

canonicalRelationalCoordinatePlusOneBoundary :
  RelationalCoordinatePlusOneBoundary
canonicalRelationalCoordinatePlusOneBoundary =
  relational-coordinate-plus-one-boundary
    true true true true
    false refl
    false refl
    false refl
    false refl
    true
    true
    false refl
    "Exact +1 arithmetic is role-indexed. Nongin frame, TSFV history residual and twistronics registration are non-arithmetic retained distinctions; their common content is only that an added distinction can defeat a coarse factorisation for a consumer that actually separates its fibres."
