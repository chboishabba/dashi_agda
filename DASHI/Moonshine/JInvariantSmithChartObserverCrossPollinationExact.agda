module DASHI.Moonshine.JInvariantSmithChartObserverCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import DASHI.Physics.Foundations.SmithChartComplexReflectionExact as Smith
import DASHI.Physics.Foundations.PhasedArrayDirectionFindingExact as Array
import DASHI.Physics.Foundations.RadioRadarGoniometerDirectionFindingExact as Goniometer
import DASHI.Moonshine.JInvariant369LevelNonDescentThroughJExact as JNoGo

------------------------------------------------------------------------
-- Shared theorem shape: a projection/readout may retain a useful coordinate
-- while failing to reconstruct the richer source state.
------------------------------------------------------------------------

record ObservationCollision
    (World Observation : Set)
    (observe : World → Observation) : Set₁ where
  field
    left right : World
    sameObservation : observe left ≡ observe right
    differentWorld : left ≡ right → ⊥

open ObservationCollision public

ObservationDeterminesWorld :
  ∀ {World Observation} →
  (World → Observation) → Set
ObservationDeterminesWorld observe =
  ∀ x y → observe x ≡ observe y → x ≡ y

collisionRefutesRecovery :
  ∀ {World Observation observe} →
  ObservationCollision World Observation observe →
  ¬ ObservationDeterminesWorld observe
collisionRefutesRecovery C exact =
  differentWorld C (exact (left C) (right C) (sameObservation C))

arrayBearingCollision :
  ObservationCollision
    Array.ArrayEmitterWorld
    Array.ArrayBearing
    Array.observeArrayBearing
arrayBearingCollision = record
  { left = Array.nearA
  ; right = Array.farA
  ; sameObservation = refl
  ; differentWorld = Array.nearAndFarArrayWorldsDistinct
  }

goniometerBearingCollision :
  ObservationCollision
    Goniometer.EmitterWorld
    Goniometer.BearingObservation
    Goniometer.observeBearing
goniometerBearingCollision = record
  { left = Goniometer.nearEmitterNorthEast
  ; right = Goniometer.farEmitterNorthEast
  ; sameObservation = refl
  ; differentWorld = Goniometer.nearAndFarWorldsDistinct
  }

smithPhaseCollisionIsProjectionNoGo :
  ∀ {F O} →
  Smith.SameSmithPhaseCollision {F = F} O →
  ¬ Smith.SmithPhaseDeterminesExactReflection O
smithPhaseCollisionIsProjectionNoGo =
  Smith.smithPhaseCollisionRefutesExactRecovery

------------------------------------------------------------------------
-- The modular result is stronger: not merely a collision witness, but a
-- transformation obstruction.  T fixes j while translating the level fibre,
-- so no decoder from j alone can recover principal-level data.
------------------------------------------------------------------------

modularLevelNoDescentUsesInvariantBaseCompiler : Bool
modularLevelNoDescentUsesInvariantBaseCompiler = true

------------------------------------------------------------------------
-- Typed role firewall.
------------------------------------------------------------------------

record JSmithArrayCrossPollinationBoundary : Set where
  constructor j-smith-array-cross-pollination-boundary
  field
    sharedComplexPhaseObserverPattern : Bool
    sharedReflectionOrInvolutionPattern : Bool
    sharedProjectionInformationLossPattern : Bool
    smithAdmittanceActsAsGammaHalfTurn : Bool
    modularLevelNoDescentStrongerThanGenericProjectionCollision : Bool
    phasedArrayUsesRelativePhaseCoordinate : Bool

    engineeringJEqualsModularJInvariant : Bool
    smithGammaEqualsModularJInvariant : Bool
    smithPhaseEqualsModularPhase : Bool
    phasedArrayRelativePhaseEqualsSmithReflectionPhase : Bool
    phasedArrayRelativePhaseEqualsModularPhase : Bool
    modularTEqualsSmithAdmittanceInvolution : Bool

canonicalJSmithArrayCrossPollinationBoundary :
  JSmithArrayCrossPollinationBoundary
canonicalJSmithArrayCrossPollinationBoundary =
  j-smith-array-cross-pollination-boundary
    true true true true true true
    false false false false false false
