module DASHI.Physics.Closure.SheetExchangeJFixedResolutionBoundary where

open import DASHI.Core.Prelude

import CRTJFixedPointBridge as CRTJ
import JFixedPoint as J
import DASHI.Physics.Closure.SU2SO3369HypervoxelBridge as SU2SO3

------------------------------------------------------------------------
-- Fixed-point-free sheet exchange is a transition carrier.  A separate
-- quotient/coarse-graining map may land on the named J scalar, but this does
-- not prove attraction, convergence, damping or universal Stage semantics.
------------------------------------------------------------------------

resolveAxisLiftToJScalar : SU2SO3.AxisLift → Nat
resolveAxisLiftToJScalar lifted =
  J.contract J.unit-obs

resolveCentralFlipInvariant :
  ∀ lifted →
  resolveAxisLiftToJScalar (SU2SO3.flipAxisLift lifted)
  ≡ resolveAxisLiftToJScalar lifted
resolveCentralFlipInvariant lifted = refl

resolveAxisLiftIs196884 :
  ∀ lifted →
  resolveAxisLiftToJScalar lifted ≡ 196884
resolveAxisLiftIs196884 lifted = J.unit-converges

resolveAxisLiftMatchesCRTPeriodPlusOne :
  ∀ lifted →
  resolveAxisLiftToJScalar lifted
  ≡ 196883 + 1
resolveAxisLiftMatchesCRTPeriodPlusOne lifted = refl

record SheetExchangeResolutionBoundary : Set₁ where
  field
    cover :
      SU2SO3.TwoSheetedCoverInterface
        SU2SO3.AxisLift
        SU2SO3.SU2Axis
    resolve : SU2SO3.AxisLift → Nat
    resolutionFlipInvariant :
      ∀ lifted →
      resolve (SU2SO3.flipAxisLift lifted) ≡ resolve lifted
    namedTarget : Nat
    targetIsJCoefficient : namedTarget ≡ 196884
    everyCanonicalLiftResolvesToTarget :
      ∀ lifted → resolve lifted ≡ namedTarget
    crtPeriodPlusOneWitness :
      196883 + 1 ≡ 196884
    quotientOrCoarseGrainingAvailable : Bool
    pureInvolutionConvergesClaimed : Bool
    attractorBasinProved : Bool
    dampingOperatorSupplied : Bool
    stage6ToStage9DynamicsProved : Bool
    observerPlusOneUniversallyReachesJClaimed : Bool

canonicalSheetExchangeResolutionBoundary :
  SheetExchangeResolutionBoundary
canonicalSheetExchangeResolutionBoundary = record
  { cover = SU2SO3.finiteAxisLiftDoubleCover
  ; resolve = resolveAxisLiftToJScalar
  ; resolutionFlipInvariant = resolveCentralFlipInvariant
  ; namedTarget = 196884
  ; targetIsJCoefficient = refl
  ; everyCanonicalLiftResolvesToTarget = resolveAxisLiftIs196884
  ; crtPeriodPlusOneWitness = CRTJ.period-plus-one
  ; quotientOrCoarseGrainingAvailable = true
  ; pureInvolutionConvergesClaimed = false
  ; attractorBasinProved = false
  ; dampingOperatorSupplied = false
  ; stage6ToStage9DynamicsProved = false
  ; observerPlusOneUniversallyReachesJClaimed = false
  }

sheetExchangeIsPeriodTwo :
  ∀ lifted →
  SU2SO3.flipAxisLift (SU2SO3.flipAxisLift lifted)
  ≡ lifted
sheetExchangeIsPeriodTwo =
  SU2SO3.flipAxisLiftInvolutive

sheetExchangeHasNoFixedPoint :
  ∀ lifted →
  ¬ (SU2SO3.flipAxisLift lifted ≡ lifted)
sheetExchangeHasNoFixedPoint =
  SU2SO3.flipAxisLiftHasNoFixedPoint
