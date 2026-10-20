module DASHI.Governance.BoloBoloNonDominationObserverSufficiencyExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.ObserverRefinementLatticeExact as Observer

------------------------------------------------------------------------
-- NON-DOMINATION / REALISED-CONTROL OBSERVER SUFFICIENCY
--
-- DASHI synthesis.  A coordination architecture can have the same aggregate
-- burden, interface capacity and backlog while differing in who actually
-- controls agenda-setting, delegation and reopening/appeal.  Therefore the
-- performance/capacity observer cannot certify the realised-control consumer.
--
-- This is a finite information-loss witness only.  Its numeric codes are
-- synthetic and do not represent an empirical Occupy, bolo, Porto Alegre or
-- Mondragon measurement.
------------------------------------------------------------------------

record GovernanceWorld : Set where
  constructor governance-world
  field
    coordinationBurden : Nat
    interfaceCapacity : Nat
    interfaceBacklog : Nat
    agendaControlCode : Nat
    delegationControlCode : Nat
    reopeningAccessCode : Nat

open GovernanceWorld public

PerformanceCapacityOutcome : Set
PerformanceCapacityOutcome = Nat × (Nat × Nat)

RealizedControlOutcome : Set
RealizedControlOutcome = Nat × (Nat × Nat)

efficiencyCapacityObserver : GovernanceWorld → PerformanceCapacityOutcome
efficiencyCapacityObserver world =
  coordinationBurden world ,
  (interfaceCapacity world , interfaceBacklog world)

realizedControlConsumer : GovernanceWorld → RealizedControlOutcome
realizedControlConsumer world =
  agendaControlCode world ,
  (delegationControlCode world , reopeningAccessCode world)

------------------------------------------------------------------------
-- Exact synthetic collision.
--
-- Both worlds have burden 60, capacity 20 and backlog 4.  Their realised
-- control differs: the left fixture codes dispersed/reopenable control while
-- the right fixture codes concentrated agenda/delegation control and a more
-- restricted reopening path.  The code values have no external semantics
-- beyond distinguishing these finite worlds.
------------------------------------------------------------------------

leftSyntheticWorld : GovernanceWorld
leftSyntheticWorld = governance-world 60 20 4 1 1 1

rightSyntheticWorld : GovernanceWorld
rightSyntheticWorld = governance-world 60 20 4 2 2 0

samePerformanceCapacityCollision :
  efficiencyCapacityObserver leftSyntheticWorld ≡
  efficiencyCapacityObserver rightSyntheticWorld
samePerformanceCapacityCollision = refl

realizedControlDiffers :
  realizedControlConsumer leftSyntheticWorld ≡
  realizedControlConsumer rightSyntheticWorld → ⊥
realizedControlDiffers ()

performanceCapacityRealizedControlNonDescent :
  Descent.ConsumerNonDescentWitness
    efficiencyCapacityObserver
    realizedControlConsumer
performanceCapacityRealizedControlNonDescent =
  Descent.consumerNonDescentWitness
    leftSyntheticWorld
    rightSyntheticWorld
    samePerformanceCapacityCollision
    realizedControlDiffers

efficiencyCapacityCannotCertifyRealizedControl :
  Descent.ConsumerSufficient
    efficiencyCapacityObserver
    realizedControlConsumer → ⊥
efficiencyCapacityCannotCertifyRealizedControl =
  Descent.nonDescentWitnessBlocksSufficiency
    performanceCapacityRealizedControlNonDescent

------------------------------------------------------------------------
-- Consumer-relative minimum information order.
--
-- The canonical realised-control consumer is least sufficient for this narrow
-- question.  Any observation surface claiming adequacy for agenda/delegation/
-- reopening control must retain enough information to refine that consumer.
------------------------------------------------------------------------

realizedControlConsumerIsLeast :
  Descent.LeastSufficientConsumerObserver realizedControlConsumer
realizedControlConsumerIsLeast =
  Descent.canonicalConsumerObserverIsLeast realizedControlConsumer

everyRealizedControlAdequateObserverRefinesCanonical :
  ∀ {Surface : Set}
    (observe : GovernanceWorld → Surface) →
  Descent.ConsumerSufficient observe realizedControlConsumer →
  Observer.Refines realizedControlConsumer observe
everyRealizedControlAdequateObserverRefinesCanonical observe sufficient =
  Descent.belowEverySufficient
    realizedControlConsumerIsLeast
    observe
    sufficient

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

record NonDominationObserverBoundary : Set where
  constructor non-domination-observer-boundary
  field
    efficiencyCapacityObserverConsumerSufficient : Bool
    realizedControlConsumerLeastSufficientPaid : Bool
    everyRealizedControlAdequateObserverRefinesCanonicalPaid : Bool
    sameCoordinationPerformanceDoesNotDetermineRealizedControl : Bool
    sameRealizedControlAutomaticallyPaysNonDominationReceipt : Bool
    realizedControlConsumerIsWorldComplete : Bool
    syntheticCollisionCreatesEmpiricalNonDominationResult : Bool
    syntheticCollisionCreatesPoliticalLegitimacy : Bool
    targetRealizedControlMeasurementStillRequired : Bool

open NonDominationObserverBoundary public

canonicalNonDominationObserverBoundary : NonDominationObserverBoundary
canonicalNonDominationObserverBoundary =
  non-domination-observer-boundary
    false
    true true true
    false false false false
    true
