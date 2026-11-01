module DASHI.Physics.ObserverConditionedMultiscaleTransportRegression where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.ObserverConditionedMultiscaleTransport

------------------------------------------------------------------------
-- Compact fail-closed regression witnesses.

observerConditioningRemainsCandidatePhysics :
  observerConditioningIsPhysicalLaw canonicalObserverWaveRoute ≡ false
observerConditioningRemainsCandidatePhysics =
  observerConditioningIsPhysicalLawIsFalse canonicalObserverWaveRoute

mdlRemainsDistinctFromPhysicalAction :
  mdlIsPhysicalAction canonicalObserverWaveRoute ≡ false
mdlRemainsDistinctFromPhysicalAction =
  mdlIsPhysicalActionIsFalse canonicalObserverWaveRoute

temporalPersistenceDoesNotProveSpeedup :
  temporalPersistenceProvesSpeedup canonicalObserverWaveRoute ≡ false
temporalPersistenceDoesNotProveSpeedup =
  temporalPersistenceProvesSpeedupIsFalse canonicalObserverWaveRoute
