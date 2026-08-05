module DASHI.Biology.FinitePadicCollapseExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Exact finite digit-plane collapse functional.  Plane support is kept
-- separate from digit orientation.  Deeper active planes receive larger
-- weights in the canonical thickness functional.

record FourPlaneSupport : Set where
  constructor fourPlaneSupport
  field
    depthZeroSupport : Nat
    depthOneSupport : Nat
    depthTwoSupport : Nat
    depthThreeSupport : Nat

open FourPlaneSupport public

activeSupportTotal : FourPlaneSupport → Nat
activeSupportTotal profile =
  depthZeroSupport profile
  + depthOneSupport profile
  + depthTwoSupport profile
  + depthThreeSupport profile

highDepthTail : FourPlaneSupport → Nat
highDepthTail profile =
  depthTwoSupport profile + depthThreeSupport profile

weightedThickness : FourPlaneSupport → Nat
weightedThickness profile =
  depthZeroSupport profile
  + 3 * depthOneSupport profile
  + 9 * depthTwoSupport profile
  + 27 * depthThreeSupport profile

unstructuredResidual : FourPlaneSupport
unstructuredResidual = fourPlaneSupport 4 3 2 1

partiallyCollapsedResidual : FourPlaneSupport
partiallyCollapsedResidual = fourPlaneSupport 4 2 1 0

collapsedResidual : FourPlaneSupport
collapsedResidual = fourPlaneSupport 4 1 0 0

unstructuredThicknessIs58 :
  weightedThickness unstructuredResidual ≡ 58
unstructuredThicknessIs58 = refl

partialThicknessIs19 :
  weightedThickness partiallyCollapsedResidual ≡ 19
partialThicknessIs19 = refl

collapsedThicknessIs7 :
  weightedThickness collapsedResidual ≡ 7
collapsedThicknessIs7 = refl

collapsedPlusTwelveIsPartial :
  weightedThickness collapsedResidual + 12
  ≡
  weightedThickness partiallyCollapsedResidual
collapsedPlusTwelveIsPartial = refl

partialPlusThirtyNineIsUnstructured :
  weightedThickness partiallyCollapsedResidual + 39
  ≡
  weightedThickness unstructuredResidual
partialPlusThirtyNineIsUnstructured = refl

collapsedHighDepthTailIsZero :
  highDepthTail collapsedResidual ≡ 0
collapsedHighDepthTailIsZero = refl

------------------------------------------------------------------------
-- A finite collapse trajectory.  The fixed point retains the coarse plane;
-- collapse is therefore not erasure of all residual structure.

data CollapseTime : Set where
  collapseTime0 : CollapseTime
  collapseTime1 : CollapseTime
  collapseTime2 : CollapseTime
  collapseTime3 : CollapseTime

collapseProfileAt : CollapseTime → FourPlaneSupport
collapseProfileAt collapseTime0 = unstructuredResidual
collapseProfileAt collapseTime1 = partiallyCollapsedResidual
collapseProfileAt collapseTime2 = collapsedResidual
collapseProfileAt collapseTime3 = collapsedResidual

collapseStabilisesAtTimeTwo :
  collapseProfileAt collapseTime2 ≡ collapseProfileAt collapseTime3
collapseStabilisesAtTimeTwo = refl

coarseResidualSurvivesCollapse :
  depthZeroSupport (collapseProfileAt collapseTime3) ≡ 4
coarseResidualSurvivesCollapse = refl

------------------------------------------------------------------------
-- Support/orientation separation for one digit plane.

data PlaneOrientation : Set where
  negativePlaneOrientation : PlaneOrientation
  positivePlaneOrientation : PlaneOrientation

data PlaneEntry : Set where
  inactivePlaneEntry : PlaneEntry
  activePlaneEntry : PlaneOrientation → PlaneEntry

isActive : PlaneEntry → Nat
isActive inactivePlaneEntry = 0
isActive (activePlaneEntry _) = 1

orientationFlipPreservesSupport :
  isActive (activePlaneEntry negativePlaneOrientation)
  ≡
  isActive (activePlaneEntry positivePlaneOrientation)
orientationFlipPreservesSupport = refl

record PadicCollapseBoundary : Set where
  constructor padicCollapseBoundary
  field
    collapseMeansAllDigitPlanesVanish : Bool
    collapseMeansAllDigitPlanesVanishIsFalse :
      collapseMeansAllDigitPlanesVanish ≡ false

    finiteThicknessDecayProvesInfiniteBorelCantelli : Bool
    finiteThicknessDecayProvesInfiniteBorelCantelliIsFalse :
      finiteThicknessDecayProvesInfiniteBorelCantelli ≡ false

    supportDeterminesOrientation : Bool
    supportDeterminesOrientationIsFalse :
      supportDeterminesOrientation ≡ false

open PadicCollapseBoundary public

canonicalPadicCollapseBoundary : PadicCollapseBoundary
canonicalPadicCollapseBoundary =
  padicCollapseBoundary false refl false refl false refl
