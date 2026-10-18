module DASHI.Physics.Quantum.CircularRydbergYangMillsAuthorityValidation where

-- RED contract: these two owners do not exist yet.
-- Production change that makes this pass:
--   * source-bounded Pultinevicius et al. circular-Rydberg lifetime owner
--   * simulator/Yang-Mills authority bridge

import DASHI.Physics.Quantum.CircularRydbergRoomTemperatureLifetimeExact as Lifetime
import DASHI.Physics.Quantum.CircularRydbergYangMillsSimulationAuthorityExact as Authority

-- The source owner must expose the three distinct experimental coordinates.
sourceDOIIsPinned = Lifetime.sourceDOIIsPinned
stateLifetimeIsNotTrapLifetime = Lifetime.stateLifetimeIsNotTrapLifetime
purcellSuppressionIsNotIntrinsicProtection = Lifetime.purcellSuppressionIsNotIntrinsicProtection

-- The authority bridge must block two invalid promotions.
lifetimeDoesNotDetermineHamiltonian = Authority.lifetimeDoesNotDetermineHamiltonian
longLifetimeDoesNotProduceYangMillsGap = Authority.longLifetimeDoesNotProduceYangMillsGap

-- Positive route: an explicit encoding/error/time witness is required before
-- the platform can be used as a bounded target-Hamiltonian simulation witness.
encodedSimulationRequiresBridge = Authority.encodedSimulationRequiresBridge
