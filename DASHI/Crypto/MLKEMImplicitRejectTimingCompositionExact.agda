module DASHI.Crypto.MLKEMImplicitRejectTimingCompositionExact where

------------------------------------------------------------------------
-- IMPLICIT-REJECTION ROUTE + TIMING OBSERVATION COMPOSITION
--
-- Primary references:
-- National Institute of Standards and Technology,
-- "Module-Lattice-Based Key-Encapsulation Mechanism Standard", FIPS 203,
-- 2024. DOI: 10.6028/NIST.FIPS.203.
--
-- Paul C. Kocher,
-- "Timing Attacks on Implementations of Diffie-Hellman, RSA, DSS, and Other
-- Systems", CRYPTO 1996. DOI: 10.1007/3-540-68697-5_9.
--
-- FIPS 203 requires the implicit-rejection comparison flag to remain secret.
-- This module shows the exact blue-team composition rule: if runtime differs
-- across two same-public hidden route states, timing itself becomes a hidden-
-- dependent observation split; if runtime is fibre-constant, route difference
-- alone creates no timing split.
--
-- The finite systems below are regressions only.  They are not claims about an
-- ML-KEM implementation.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)

import DASHI.Crypto.MLKEMImplicitRejectProtocolObservationExact as Route
import DASHI.Crypto.TimingObservationSideChannelExact as Timing
import DASHI.Crypto.ChosenCiphertextObservationRefinementExact as Observation

routeRuntime : Route.DecapsulationRoute → ⊤ → Nat
routeRuntime Route.candidateRoute query = 1
routeRuntime Route.fallbackRoute query = 2

routeTimedSystem : Timing.TimedPublicSystem
routeTimedSystem =
  Timing.timedPublicSystem
    Route.DecapsulationRoute
    ⊤
    ⊤
    (λ hidden → tt)
    routeRuntime

routeTimingSplit : Timing.TimingSplit routeTimedSystem
routeTimingSplit =
  Timing.timingSplit
    Route.candidateRoute
    Route.fallbackRoute
    refl
    tt
    different
  where
  different : 1 ≡ 2 → ⊥
  different ()

routeTimingIsHiddenDependent :
  Observation.ObservationSplitWitness
    (Timing.timingObservationSystem routeTimedSystem)
routeTimingIsHiddenDependent =
  Timing.timingSplitGivesObservationSplit routeTimingSplit

------------------------------------------------------------------------
-- Constant-time route regression.
------------------------------------------------------------------------

constantRouteRuntime : Route.DecapsulationRoute → ⊤ → Nat
constantRouteRuntime hidden query = 1

constantRouteTimedSystem : Timing.TimedPublicSystem
constantRouteTimedSystem =
  Timing.timedPublicSystem
    Route.DecapsulationRoute
    ⊤
    ⊤
    (λ hidden → tt)
    constantRouteRuntime

constantRouteTiming : Timing.FibreConstantTiming constantRouteTimedSystem
constantRouteTiming =
  Timing.fibreConstantTiming
    (λ {left} {right} samePublic q → refl)

constantRouteHasNoTimingSplit : Timing.TimingSplit constantRouteTimedSystem → ⊥
constantRouteHasNoTimingSplit split =
  Timing.timingSplitRefutesFibreConstant split constantRouteTiming

------------------------------------------------------------------------
-- Boundary: route-dependent runtime is sufficient to define a timing split in
-- this regression, but no such split is asserted for a conforming ML-KEM
-- implementation without an actual measurement/implementation witness.
------------------------------------------------------------------------
