module DASHI.Architecture.AgentRelativeAffordanceExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- AGENT-RELATIVE AFFORDANCE
--
-- Architectural usability is not identified with geometry.  A geometric
-- connection can be usable for one agent and unusable for another.
------------------------------------------------------------------------

record AffordanceSystem : Set₁ where
  field
    Environment : Set
    Agent       : Set
    Activity    : Set

    GeometricallyReachable : Environment → Activity → Set
    Affords                : Environment → Agent → Activity → Set

open AffordanceSystem public

data Environment : Set where
  stairOnlyConnection : Environment

data Agent : Set where
  stairUser stepFreeUser : Agent

data Activity : Set where
  reachUpperLevel : Activity

GeometricReachability : Environment → Activity → Set
GeometricReachability stairOnlyConnection reachUpperLevel = ⊤

UsableAffordance : Environment → Agent → Activity → Set
UsableAffordance stairOnlyConnection stairUser reachUpperLevel = ⊤
UsableAffordance stairOnlyConnection stepFreeUser reachUpperLevel = ⊥

architectureAffordanceSystem : AffordanceSystem
architectureAffordanceSystem =
  record
    { Environment = Environment
    ; Agent = Agent
    ; Activity = Activity
    ; GeometricallyReachable = GeometricReachability
    ; Affords = UsableAffordance
    }

geometricallyReachable :
  GeometricallyReachable architectureAffordanceSystem
    stairOnlyConnection reachUpperLevel
geometricallyReachable = tt

usableForOneAgent :
  Affords architectureAffordanceSystem
    stairOnlyConnection stairUser reachUpperLevel
usableForOneAgent = tt

notUsableForOtherAgent :
  Affords architectureAffordanceSystem
    stairOnlyConnection stepFreeUser reachUpperLevel → ⊥
notUsableForOtherAgent affordance = affordance

geometricReachabilityDoesNotImplyAgentRelativeUsability :
  GeometricallyReachable architectureAffordanceSystem
      stairOnlyConnection reachUpperLevel
  ×
  (Affords architectureAffordanceSystem
      stairOnlyConnection stepFreeUser reachUpperLevel → ⊥)
geometricReachabilityDoesNotImplyAgentRelativeUsability =
  geometricallyReachable , notUsableForOtherAgent
