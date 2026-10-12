module DASHI.Physics.Plasma.Phase243ConsumerDescentRegression where

open import DASHI.Core.Prelude

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Physics.Plasma.Phase243OrbitQuotientExact as Q54
import DASHI.Physics.Plasma.Phase243ConsumerDescentExact as PhaseDescent

consumerInvariantUnderPaidPhaseActionDescends :
  ∀ {Outcome : Set} →
  (c : PhaseDescent.PhaseInvariantConsumer Outcome) →
  Descent.FactorsThrough Q54.quotientCore (PhaseDescent.consumer c)
consumerInvariantUnderPaidPhaseActionDescends =
  PhaseDescent.phaseInvariantConsumerFactorsThroughCore54
