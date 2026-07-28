module DASHI.Physics.Closure.SheetExchangeJFixedResolutionBoundary where

open import DASHI.Core.Prelude

import CRTJFixedPointBridge as CRTJ
import JFixedPoint as J
import DASHI.Physics.Closure.SU2SO3369HypervoxelBridge as SU2SO3

------------------------------------------------------------------------
-- Fixed-point-free sheet exchange is a transition carrier.
--
-- The map below is intentionally a constant, centre-blind quotient label: it
-- forgets the lifted value and sends the whole finite cover to the existing J
-- scalar. It is not a lift-sensitive resolution algorithm, convergence map,
-- damping operator or attractor theorem.
------------------------------------------------------------------------

constantJScalarQuotient : SU2SO3.AxisLift → Nat
constantJScalarQuotient lifted =
  J.contract J.unit-obs

constantQuotientCentralFlipInvariant :
  ∀ lifted →
  constantJScalarQuotient (SU2SO3.flipAxisLift lifted)
  ≡ constantJScalarQuotient lifted
constantQuotientCentralFlipInvariant lifted = refl

constantQuotientCoverFlipInvariant :
  ∀ lifted →
  constantJScalarQuotient
    (SU2SO3.TwoSheetedCoverInterface.centralFlip
      SU2SO3.finiteAxisLiftDoubleCover
      lifted)
  ≡ constantJScalarQuotient lifted
constantQuotientCoverFlipInvariant lifted = refl

constantQuotientIs196884 :
  ∀ lifted →
  constantJScalarQuotient lifted ≡ 196884
constantQuotientIs196884 lifted = J.unit-converges

constantQuotientMatchesCRTPeriodPlusOne :
  ∀ lifted →
  constantJScalarQuotient lifted
  ≡ 196883 + 1
constantQuotientMatchesCRTPeriodPlusOne lifted = refl

record SheetExchangeResolutionBoundary : Set₁ where
  field
    cover :
      SU2SO3.TwoSheetedCoverInterface
        SU2SO3.AxisLift
        SU2SO3.SU2Axis
    quotientToJScalar : SU2SO3.AxisLift → Nat
    quotientFlipInvariant :
      ∀ lifted →
      quotientToJScalar
        (SU2SO3.TwoSheetedCoverInterface.centralFlip cover lifted)
      ≡ quotientToJScalar lifted
    namedTarget : Nat
    targetIsJCoefficient : namedTarget ≡ 196884
    everyLiftHasSameQuotientTarget :
      ∀ lifted → quotientToJScalar lifted ≡ namedTarget
    crtPeriodPlusOneWitness :
      196883 + 1 ≡ 196884
    constantQuotientIntentional : Bool
    quotientIsLiftSensitive : Bool
    quotientOrCoarseGrainingLabelAvailable : Bool
    pureInvolutionConvergesClaimed : Bool
    attractorBasinProved : Bool
    dampingOperatorSupplied : Bool
    stage6ToStage9DynamicsProved : Bool
    observerPlusOneUniversallyReachesJClaimed : Bool

canonicalSheetExchangeResolutionBoundary :
  SheetExchangeResolutionBoundary
canonicalSheetExchangeResolutionBoundary = record
  { cover = SU2SO3.finiteAxisLiftDoubleCover
  ; quotientToJScalar = constantJScalarQuotient
  ; quotientFlipInvariant = constantQuotientCoverFlipInvariant
  ; namedTarget = 196884
  ; targetIsJCoefficient = refl
  ; everyLiftHasSameQuotientTarget = constantQuotientIs196884
  ; crtPeriodPlusOneWitness = CRTJ.period-plus-one
  ; constantQuotientIntentional = true
  ; quotientIsLiftSensitive = false
  ; quotientOrCoarseGrainingLabelAvailable = true
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
