module DASHI.GameTheory.RepeatedStrategicLearningMemoryBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.GameTheory.StrategicInteractionCoreExact as Game
import DASHI.Cognition.PNF.MemoryFibre as Memory
import DASHI.Cognition.PNF.LearningAlgebra as Learning

------------------------------------------------------------------------
-- REPEATED STRATEGIC LEARNING / MEMORY BRIDGE
--
-- One-shot strategic stability does not determine adaptation through repeated
-- interaction.  This bridge reuses versioned memory and learning receipts so a
-- player's current strategy may depend on retained history without overwriting
-- the remembered event.  It does not claim subgame-perfect equilibrium,
-- Bayesian updating, perfect monitoring, or rational learning automatically.
------------------------------------------------------------------------

record RepeatedStrategicLearningProcess
    (G : Game.StrategicGame) : Set₁ where
  constructor repeated-strategic-learning-process
  field
    Time : Set
    next : Time → Time

    profileAt : Time → Game.Profile G
    memoryAt : Game.Player G → Time → Memory.VersionedMemory

    strategyFromMemory :
      (player : Game.Player G) →
      Memory.VersionedMemory →
      Game.Strategy G player

    profileStrategyTracksMemory :
      (player : Game.Player G) →
      (time : Time) →
      Game.strategyAt G (profileAt time) player
      ≡ strategyFromMemory player (memoryAt player time)

    learningStep :
      (player : Game.Player G) →
      (time : Time) →
      Learning.LearningReceipt

    learningStartsFromCurrentMemory :
      (player : Game.Player G) →
      (time : Time) →
      Learning.before (learningStep player time)
      ≡ Memory.current (memoryAt player time)

    nextMemoryCurrentMatchesLearning :
      (player : Game.Player G) →
      (time : Time) →
      Memory.current (memoryAt player (next time))
      ≡ Learning.after (learningStep player time)

    processReference : String
    historyReference : String
    strategyUpdateReference : String

open RepeatedStrategicLearningProcess public

record StagewiseNashPath
    {G : Game.StrategicGame}
    (R : RepeatedStrategicLearningProcess G) : Set₁ where
  constructor stagewise-nash-path
  field
    equilibriumAt :
      (time : Time R) → Game.NashEquilibrium G

    equilibriumProfileMatchesPath :
      (time : Time R) →
      Game.profile (equilibriumAt time) ≡ profileAt R time

    equilibriumReference : String

open StagewiseNashPath public

------------------------------------------------------------------------
-- A strategic change can coexist with memory-content preservation.  The
-- learning owner already distinguishes revaluation, habituation, reinforcement,
-- extinction and phase realignment; this layer merely binds those receipts to
-- the strategy path.
------------------------------------------------------------------------

record StrategicLearningTransition
    {G : Game.StrategicGame}
    (R : RepeatedStrategicLearningProcess G)
    (player : Game.Player G)
    (time : Time R) : Set₁ where
  constructor strategic-learning-transition
  field
    beforeStrategy : Game.Strategy G player
    afterStrategy : Game.Strategy G player

    beforeStrategyMatches :
      beforeStrategy ≡ Game.strategyAt G (profileAt R time) player

    afterStrategyMatches :
      afterStrategy ≡ Game.strategyAt G (profileAt R (next R time)) player

    memoryUpdate : Learning.LearningReceipt
    memoryUpdateMatchesProcess :
      memoryUpdate ≡ learningStep R player time

    transitionReference : String

open StrategicLearningTransition public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data StagewiseNashMeansRepeatedGameEquilibriumPermission : Set where

data LearningMeansBestResponsePermission : Set where

data MemoryMeansPerfectMonitoringPermission : Set where

data ExtinctionMeansForgettingPermission : Set where

data ReinforcementMeansUtilityMaximisationPermission : Set where

data RepeatedInteractionMeansCooperationPermission : Set where

data RememberedHarmMeansRetaliationPermission : Set where

data StrategyChangeMeansPreferenceChangePermission : Set where

stagewiseNashDoesNotAutomaticallyGiveRepeatedGameEquilibrium :
  StagewiseNashMeansRepeatedGameEquilibriumPermission → ⊥
stagewiseNashDoesNotAutomaticallyGiveRepeatedGameEquilibrium ()

learningDoesNotAutomaticallyMeanBestResponse :
  LearningMeansBestResponsePermission → ⊥
learningDoesNotAutomaticallyMeanBestResponse ()

memoryDoesNotAutomaticallyMeanPerfectMonitoring :
  MemoryMeansPerfectMonitoringPermission → ⊥
memoryDoesNotAutomaticallyMeanPerfectMonitoring ()

extinctionDoesNotMeanForgetting : ExtinctionMeansForgettingPermission → ⊥
extinctionDoesNotMeanForgetting ()

reinforcementDoesNotAutomaticallyMeanUtilityMaximisation :
  ReinforcementMeansUtilityMaximisationPermission → ⊥
reinforcementDoesNotAutomaticallyMeanUtilityMaximisation ()

repetitionDoesNotAutomaticallyProduceCooperation :
  RepeatedInteractionMeansCooperationPermission → ⊥
repetitionDoesNotAutomaticallyProduceCooperation ()

rememberedHarmDoesNotLicenseRetaliation :
  RememberedHarmMeansRetaliationPermission → ⊥
rememberedHarmDoesNotLicenseRetaliation ()

strategyChangeDoesNotAutomaticallyMeanPreferenceChange :
  StrategyChangeMeansPreferenceChangePermission → ⊥
strategyChangeDoesNotAutomaticallyMeanPreferenceChange ()

record RepeatedStrategicLearningBoundary : Set where
  constructor repeated-strategic-learning-boundary
  field
    strategyCanDependOnVersionedMemory : Bool
    learningReceiptDrivesMemoryTransition : Bool
    memoryOverwriteForbiddenRemainsAvailable : Bool
    stagewiseNashSeparateFromRepeatedEquilibrium : Bool
    learningSeparateFromBestResponse : Bool
    rememberedHarmAutomaticallyLicensesRetaliation : Bool

canonicalRepeatedStrategicLearningBoundary : RepeatedStrategicLearningBoundary
canonicalRepeatedStrategicLearningBoundary =
  repeated-strategic-learning-boundary true true true true true false
