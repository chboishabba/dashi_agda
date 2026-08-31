module DASHI.Analysis.RiemannAristotlePoleNearPhaseStatisticExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- DIRECT ROUTE: MINIMUM PHASE-SENSITIVE INFORMATION
--
-- The direct finite-near route cannot descend through count/envelope data.
-- What it needs is an additional statistic that still sees the target-relative
-- phase entering
--
--   cos((b_sigma - t) u).
--
-- This file does not invent such a statistic analytically.  It types the exact
-- information interface that any successful direct theorem must provide.
------------------------------------------------------------------------

record PoleNearPhaseStatistic : Set₁ where
  constructor pole-near-phase-statistic
  field
    ZeroIndex Scalar PhaseCode : Set
    target : Scalar
    cutoff : Scalar
    nearIndex : ZeroIndex → Set
    multiplicity : ZeroIndex → Scalar
    targetRelativeGap : ZeroIndex → Scalar
    phaseCode : ZeroIndex → PhaseCode

    SameCoarseObservation : ZeroIndex → ZeroIndex → Set
    DistinguishesSignedContribution : PhaseCode → PhaseCode → Set

    phaseCanSeparateCoarseCollision :
      (x y : ZeroIndex) →
      SameCoarseObservation x y →
      DistinguishesSignedContribution (phaseCode x) (phaseCode y) → Set

    preservesTargetRelativeGap : Set
    preservesMultiplicity : Set
    preservesFiniteNearIndex : Set
    phaseReference : String

open PoleNearPhaseStatistic public

record PhaseStatisticControlsFiniteNear
    (p : PoleNearPhaseStatistic) : Set₁ where
  constructor phase-statistic-controls-finite-near
  field
    Evaluation : Set
    evaluation : Evaluation
    controlReference : String

open PhaseStatisticControlsFiniteNear public

record PoleNearPhaseStatisticBoundary : Set where
  constructor pole-near-phase-statistic-boundary
  field
    countAndEnvelopeSufficient : Bool
    countAndEnvelopeSufficientIsFalse : countAndEnvelopeSufficient ≡ false

    targetRelativePhaseCoordinateRequired : Bool
    targetRelativePhaseCoordinateRequiredIsTrue :
      targetRelativePhaseCoordinateRequired ≡ true

    repositoryAlreadyOwnsConcretePoleNearPhaseStatistic : Bool
    repositoryAlreadyOwnsConcretePoleNearPhaseStatisticIsFalse :
      repositoryAlreadyOwnsConcretePoleNearPhaseStatistic ≡ false

    directFiniteNearClosed : Bool
    directFiniteNearClosedIsFalse : directFiniteNearClosed ≡ false

    nextTheorem : String

canonicalPoleNearPhaseStatisticBoundary : PoleNearPhaseStatisticBoundary
canonicalPoleNearPhaseStatisticBoundary =
  pole-near-phase-statistic-boundary
    false refl
    true refl
    false refl
    false refl
    "Construct a source-native target-relative phase statistic for zeros in nearOffFinset(t,J), and prove that it controls the literal reflection-paired finite pole-near signed evaluation strongly enough to yield the required approximant/error receipt."
