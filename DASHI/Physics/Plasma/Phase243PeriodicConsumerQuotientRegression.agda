module DASHI.Physics.Plasma.Phase243PeriodicConsumerQuotientRegression where

open import DASHI.Core.Prelude

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Physics.Plasma.Phase243OrbitQuotientExact as Q54
import DASHI.Physics.Plasma.Phase243PeriodicConsumerQuotientExact as Periodic

periodicReparameterizationInvariantConsumerMaySearchCore54 :
  ∀ {PhysicalState Observation : Set} →
  (r : Periodic.PeriodicPhase243Realization PhysicalState Observation) →
  Descent.FactorsThrough
    Q54.quotientCore
    (Periodic.realizedObservation r)
periodicReparameterizationInvariantConsumerMaySearchCore54 =
  Periodic.periodicRealizationFactorsThroughCore54
