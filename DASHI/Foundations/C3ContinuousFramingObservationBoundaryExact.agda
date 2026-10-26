module DASHI.Foundations.C3ContinuousFramingObservationBoundaryExact where

-- A continuous phase cannot be recovered from position samples or terminal
-- orientation alone without path/regularity/transport assumptions.
-- A separate unwrapped angular lift records full turns.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong)
open import Data.Empty using (⊥)

import DASHI.Foundations.C3NineSiteAlternatingOrbitExact as Orbit
import DASHI.Foundations.C3NineSiteSixStepMirrorExact as Mirror

record AngularCarrier : Set₁ where
  field
    Angle : Set
    UnwrappedAngle : Set
    phase : UnwrappedAngle → Angle
    FullTurn : UnwrappedAngle → UnwrappedAngle
    phasePeriod : (u : UnwrappedAngle) →
      phase (FullTurn u) ≡ phase u

-- For practical continuous fibre reconstruction, this must be instantiated
-- by a continuous path lift R -> S1, with a specified initial lift, or a
-- principal U(1) connection and parallel transport data.
record ContinuousFramedThreeStrands : Set₁ where
  field
    Time : Set
    Vector : Set
    Angle : Set
    UnwrappedAngle : Set
    position : Orbit.Site → Time → Vector
    tangent : Orbit.Site → Time → Vector
    transverse : Orbit.Site → Time → Vector
    phase : UnwrappedAngle → Angle
    lift : Orbit.Site → Time → UnwrappedAngle
    collisionFree : (t : Time) → Set
    unitTransverse : (s : Orbit.Site) (t : Time) → Set
    orthogonal : (s : Orbit.Site) (t : Time) → Set
    regularity : Set
    transportLaw : Set
    reconstructionBound : Set

-- Typed no-go example for a finite end observation. A discrete twist
-- counter differs, while observable site + orientation can be the same.
record EndpointTurnState : Set where
  constructor endpoint
  field
    site : Orbit.Site
    fullTurns : Nat

observedEnd : EndpointTurnState → Orbit.Site
observedEnd = EndpointTurnState.site

zeroTurn : EndpointTurnState
zeroTurn = endpoint Orbit.TL zero

oneTurn : EndpointTurnState
oneTurn = endpoint Orbit.TL (suc zero)

sameObservedEnd : observedEnd zeroTurn ≡ observedEnd oneTurn
sameObservedEnd = refl

zero≢one : zero ≡ suc zero → ⊥
zero≢one ()

differentTurnStates : zeroTurn ≡ oneTurn → ⊥
differentTurnStates equality = zero≢one (cong EndpointTurnState.fullTurns equality)

-- The mirror action on signed grid coordinates does NOT specify the lift
-- of the frame angle; a physical action and a framing convention are needed.
record ReflectionFrameLift (A : AngularCarrier) : Set₁ where
  field
    reflectAngle : AngularCarrier.Angle A → AngularCarrier.Angle A
    reflectLift : AngularCarrier.UnwrappedAngle A →
                  AngularCarrier.UnwrappedAngle A
    compatible : (x : AngularCarrier.UnwrappedAngle A) →
      AngularCarrier.phase A (reflectLift x) ≡
      reflectAngle (AngularCarrier.phase A x)
    involutivePhase : (a : AngularCarrier.Angle A) →
      reflectAngle (reflectAngle a) ≡ a
