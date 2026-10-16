module DASHI.Cognition.OpenCivilianSpatialDefenseConsumerSufficiencyExact where

open import DASHI.Core.Prelude

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Physics.Foundations.RadioRadarGoniometerDirectionFindingExact as Goniometer

------------------------------------------------------------------------
-- CONSUMER-RELATIVE SUFFICIENCY FOR CIVILIAN RF OBSERVATION
--
-- The exact emitter/world state is used here only as a synthetic consumer to
-- prove a non-descent result already implicit in the goniometer model: one
-- bearing cannot determine a richer world that contains range/identity-like
-- distinctions.  This is a mathematical reconstruction, not a source claim
-- about any particular robot, venue, radio, or operational deployment.
------------------------------------------------------------------------

exactEmitterWorldConsumer :
  Goniometer.EmitterWorld → Goniometer.EmitterWorld
exactEmitterWorldConsumer world = world

singleBearingExactWorldNonDescent :
  Descent.ConsumerNonDescentWitness
    Goniometer.observeBearing
    exactEmitterWorldConsumer
singleBearingExactWorldNonDescent =
  Descent.consumerNonDescentWitness
    Goniometer.nearEmitterNorthEast
    Goniometer.farEmitterNorthEast
    refl
    Goniometer.nearAndFarWorldsDistinct

singleBearingCannotFactorExactWorld :
  Descent.FactorsThrough
    Goniometer.observeBearing
    exactEmitterWorldConsumer →
  ⊥
singleBearingCannotFactorExactWorld =
  Descent.nonDescentWitnessBlocksFactorization
    singleBearingExactWorldNonDescent

singleBearingCannotBeExactWorldSufficient :
  Descent.ConsumerSufficient
    Goniometer.observeBearing
    exactEmitterWorldConsumer →
  ⊥
singleBearingCannotBeExactWorldSufficient =
  Descent.nonDescentWitnessBlocksSufficiency
    singleBearingExactWorldNonDescent

singleBearingExactWorldNonDescentPaid : Bool
singleBearingExactWorldNonDescentPaid = true

consumerDescentMinimalObserverCoreReused : Bool
consumerDescentMinimalObserverCoreReused = true

bearingSufficiencyMeansWorldCompleteness : Bool
bearingSufficiencyMeansWorldCompleteness = false

oneObservationIsLeastIntrusiveForEveryConsumer : Bool
oneObservationIsLeastIntrusiveForEveryConsumer = false

------------------------------------------------------------------------
-- Operational implication boundary.
--
-- A non-descent witness identifies missing information for a consumer.  It
-- does not say what sensor must be added, authorize more intrusive collection,
-- or create a right to identify or track a person/device.
------------------------------------------------------------------------

nonDescentCreatesNewCollectionAuthority : Bool
nonDescentCreatesNewCollectionAuthority = false

nonDescentCreatesIdentityResolutionAuthority : Bool
nonDescentCreatesIdentityResolutionAuthority = false

nonDescentCreatesTargetingAuthority : Bool
nonDescentCreatesTargetingAuthority = false

record CivilianConsumerSufficiencyBoundary : Set where
  constructor civilian-consumer-sufficiency-boundary
  field
    singleBearingFailsExactWorldConsumer : Bool
    consumerRelativeMinimalityReused : Bool
    insufficiencyAuthorizesMoreCollection : Bool
    insufficiencyAuthorizesIdentityResolution : Bool
    insufficiencyAuthorizesTargeting : Bool

canonicalCivilianConsumerSufficiencyBoundary :
  CivilianConsumerSufficiencyBoundary
canonicalCivilianConsumerSufficiencyBoundary =
  civilian-consumer-sufficiency-boundary
    true true false false false
