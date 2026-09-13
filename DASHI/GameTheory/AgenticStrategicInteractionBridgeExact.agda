module DASHI.GameTheory.AgenticStrategicInteractionBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.GameTheory.StrategicInteractionCoreExact as Game
import DASHI.Biology.AgenticMaterialsControlCore as Agentic

------------------------------------------------------------------------
-- AGENTIC / STRATEGIC REALISATION
--
-- A game strategy may realise an AgenticMaterial action, but strategic
-- preference and target-relative defect improvement remain separate until an
-- explicit alignment receipt is supplied.
------------------------------------------------------------------------

record AgenticStrategicRealisation
    (G : Game.StrategicGame)
    (M : Agentic.AgenticMaterial) : Set₁ where
  constructor agentic-strategic-realisation
  field
    player : Game.Player G

    stateForProfile : Game.Profile G → Agentic.State M
    observationForProfile : Game.Profile G → Agentic.Observation M
    strategyToAction : Game.Strategy G player → Agentic.Action M
    outcomeToState : Game.Outcome G → Agentic.State M

    observationRealises :
      (profile : Game.Profile G) →
      observationForProfile profile
      ≡ Agentic.observe M (stateForProfile profile)

    currentStrategyRealisesPolicy :
      (profile : Game.Profile G) →
      strategyToAction (Game.strategyAt G profile player)
      ≡ Agentic.policy M (observationForProfile profile)

    gameOutcomeRealisesActuatedState :
      (profile : Game.Profile G) →
      outcomeToState (Game.outcome G profile)
      ≡ Agentic.actuate M
          (strategyToAction (Game.strategyAt G profile player))
          (stateForProfile profile)

    realisationReference : String

open AgenticStrategicRealisation public

record StrategicPreferenceDefectAlignment
    {G : Game.StrategicGame}
    {M : Agentic.AgenticMaterial}
    (R : AgenticStrategicRealisation G M) : Set₁ where
  constructor strategic-preference-defect-alignment
  field
    strictPreferenceImprovesDefect :
      (left right : Game.Outcome G) →
      Game.StrictlyPrefers G (player R) left right →
      Agentic.better M
        (Agentic.defect M (outcomeToState R left))
        (Agentic.defect M (outcomeToState R right))

    alignmentReference : String

open StrategicPreferenceDefectAlignment public

profitableDeviationImprovesAlignedDefect :
  ∀ {G M}
    {R : AgenticStrategicRealisation G M} →
  (A : StrategicPreferenceDefectAlignment R) →
  (profile : Game.Profile G) →
  (alternative : Game.Strategy G (player R)) →
  Game.ProfitableDeviation G profile (player R) alternative →
  Agentic.better M
    (Agentic.defect M
      (outcomeToState R
        (Game.deviationOutcome G profile (player R) alternative)))
    (Agentic.defect M (outcomeToState R (Game.outcome G profile)))
profitableDeviationImprovesAlignedDefect {G = G} {R = R}
  A profile alternative profitable =
  strictPreferenceImprovesDefect A
    (Game.deviationOutcome G profile (player R) alternative)
    (Game.outcome G profile)
    profitable

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data AgenticPolicyMeansBestResponsePermission : Set where

data BestResponseMeansAgenticCorrectionPermission : Set where

data NashMeansAgenticTargetPermission : Set where

data StrategicPreferenceMeansDefectOrderPermission : Set where

data GameOutcomeMeansPhysicalStateIdentityPermission : Set where

agenticPolicyDoesNotAutomaticallyMeanBestResponse :
  AgenticPolicyMeansBestResponsePermission → ⊥
agenticPolicyDoesNotAutomaticallyMeanBestResponse ()

bestResponseDoesNotAutomaticallyMeanCorrectiveAction :
  BestResponseMeansAgenticCorrectionPermission → ⊥
bestResponseDoesNotAutomaticallyMeanCorrectiveAction ()

nashDoesNotAutomaticallyMeanAgenticTarget :
  NashMeansAgenticTargetPermission → ⊥
nashDoesNotAutomaticallyMeanAgenticTarget ()

strategicPreferenceNeedsDefectAlignment :
  StrategicPreferenceMeansDefectOrderPermission → ⊥
strategicPreferenceNeedsDefectAlignment ()

gameOutcomeDoesNotBecomePhysicalStateWithoutRealisation :
  GameOutcomeMeansPhysicalStateIdentityPermission → ⊥
gameOutcomeDoesNotBecomePhysicalStateWithoutRealisation ()

record AgenticStrategicBoundary : Set where
  constructor agentic-strategic-boundary
  field
    strategyActionRealisationExplicit : Bool
    observationPolicyPathExplicit : Bool
    outcomeStateRealisationExplicit : Bool
    preferenceDefectAlignmentOptional : Bool
    nashAutomaticallyMeansTarget : Bool

canonicalAgenticStrategicBoundary : AgenticStrategicBoundary
canonicalAgenticStrategicBoundary =
  agentic-strategic-boundary true true true true false
