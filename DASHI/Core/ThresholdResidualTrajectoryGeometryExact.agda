module DASHI.Core.ThresholdResidualTrajectoryGeometryExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- THRESHOLD STATUS / RESIDUAL MAGNITUDE / TRAJECTORY GEOMETRY
--
-- Generic finite arithmetic for systems with threshold-oriented coordinates.
-- A binary threshold judgement, a distance from threshold, an aggregate
-- residual and a trajectory judgement are distinct observers.
------------------------------------------------------------------------

data Orientation : Set where
  higherIsBetter lowerIsBetter : Orientation

_≤ᵇ_ : Nat → Nat → Bool
zero ≤ᵇ n = true
suc m ≤ᵇ zero = false
suc m ≤ᵇ suc n = m ≤ᵇ n

record ThresholdObservation : Set where
  constructor thresholdObservation
  field
    orientation : Orientation
    threshold : Nat
    value : Nat

open ThresholdObservation public

withinThreshold : ThresholdObservation → Bool
withinThreshold (thresholdObservation higherIsBetter t v) = t ≤ᵇ v
withinThreshold (thresholdObservation lowerIsBetter t v) = v ≤ᵇ t

thresholdResidual : ThresholdObservation → Nat
thresholdResidual (thresholdObservation higherIsBetter t v) = t ∸ v
thresholdResidual (thresholdObservation lowerIsBetter t v) = v ∸ t

------------------------------------------------------------------------
-- Same threshold status does not identify distance from threshold.
------------------------------------------------------------------------

nearHigherFailure farHigherFailure : ThresholdObservation
nearHigherFailure = thresholdObservation higherIsBetter 10 9
farHigherFailure  = thresholdObservation higherIsBetter 10 1

sameHigherFailureStatus :
  withinThreshold nearHigherFailure ≡ withinThreshold farHigherFailure
sameHigherFailureStatus = refl

nearHigherResidual : thresholdResidual nearHigherFailure ≡ 1
nearHigherResidual = refl

farHigherResidual : thresholdResidual farHigherFailure ≡ 9
farHigherResidual = refl

sameStatusDoesNotRecoverResidual :
  thresholdResidual nearHigherFailure ≡
  thresholdResidual farHigherFailure → ⊥
sameStatusDoesNotRecoverResidual ()

nearLowerFailure farLowerFailure : ThresholdObservation
nearLowerFailure = thresholdObservation lowerIsBetter 10 11
farLowerFailure  = thresholdObservation lowerIsBetter 10 19

sameLowerFailureStatus :
  withinThreshold nearLowerFailure ≡ withinThreshold farLowerFailure
sameLowerFailureStatus = refl

------------------------------------------------------------------------
-- Aggregate residual is another lossy observer.
------------------------------------------------------------------------

record TwoCoordinateResidual : Set where
  constructor twoCoordinateResidual
  field
    firstResidual secondResidual : Nat

open TwoCoordinateResidual public

aggregateResidual : TwoCoordinateResidual → Nat
aggregateResidual r = firstResidual r + secondResidual r

residualA residualB : TwoCoordinateResidual
residualA = twoCoordinateResidual 1 0
residualB = twoCoordinateResidual 0 1

sameAggregateResidual :
  aggregateResidual residualA ≡ aggregateResidual residualB
sameAggregateResidual = refl

sameAggregateDoesNotRecoverFirstCoordinate :
  firstResidual residualA ≡ firstResidual residualB → ⊥
sameAggregateDoesNotRecoverFirstCoordinate ()

------------------------------------------------------------------------
-- Two-domain trajectory shadow.
--
-- This keeps social-style shortfall and ecological-style overshoot independent.
-- A move may improve one coordinate while worsening the other.  No scalar
-- compensation principle is built in.
------------------------------------------------------------------------

record DualResidualState : Set where
  constructor dualResidualState
  field
    shortfall : Nat
    overshoot : Nat

open DualResidualState public

jointResidual : DualResidualState → Nat
jointResidual s = shortfall s + overshoot s

trajectoryStart socialBetterEcoWorse ecoBetterSocialWorse : DualResidualState
trajectoryStart = dualResidualState 3 3
socialBetterEcoWorse = dualResidualState 2 4
ecoBetterSocialWorse = dualResidualState 4 2

socialImprovesInFirstWitness :
  shortfall socialBetterEcoWorse ≡ 2
socialImprovesInFirstWitness = refl

ecologicalWorsensInFirstWitness :
  overshoot socialBetterEcoWorse ≡ 4
ecologicalWorsensInFirstWitness = refl

sameJointResidualDespiteTradeoff :
  jointResidual trajectoryStart ≡ jointResidual socialBetterEcoWorse
sameJointResidualDespiteTradeoff = refl

oppositeTradeoffSameAggregate :
  jointResidual socialBetterEcoWorse ≡ jointResidual ecoBetterSocialWorse
oppositeTradeoffSameAggregate = refl

sameAggregateDoesNotRecoverShortfall :
  shortfall socialBetterEcoWorse ≡ shortfall ecoBetterSocialWorse → ⊥
sameAggregateDoesNotRecoverShortfall ()

record ThresholdTrajectoryBoundary : Set where
  constructor thresholdTrajectoryBoundary
  field
    thresholdStatusDeterminesResidualMagnitude : Bool
    thresholdStatusDeterminesResidualMagnitudeIsFalse :
      thresholdStatusDeterminesResidualMagnitude ≡ false
    aggregateResidualDeterminesCoordinateResiduals : Bool
    aggregateResidualDeterminesCoordinateResidualsIsFalse :
      aggregateResidualDeterminesCoordinateResiduals ≡ false
    improvementOnOneAxisForcesImprovementOnOther : Bool
    improvementOnOneAxisForcesImprovementOnOtherIsFalse :
      improvementOnOneAxisForcesImprovementOnOther ≡ false
    aggregateEqualityMeansSameTrajectoryMeaning : Bool
    aggregateEqualityMeansSameTrajectoryMeaningIsFalse :
      aggregateEqualityMeansSameTrajectoryMeaning ≡ false

canonicalThresholdTrajectoryBoundary : ThresholdTrajectoryBoundary
canonicalThresholdTrajectoryBoundary =
  thresholdTrajectoryBoundary false refl false refl false refl false refl
