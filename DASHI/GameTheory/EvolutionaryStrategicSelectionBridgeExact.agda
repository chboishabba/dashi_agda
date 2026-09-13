module DASHI.GameTheory.EvolutionaryStrategicSelectionBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.GameTheory.StrategicInteractionCoreExact as Game
import DASHI.Biology.Evolution.EvolutionaryPopulationDynamics as Evolution

------------------------------------------------------------------------
-- EVOLUTIONARY / STRATEGIC REALISATION
--
-- The evolutionary owner already has environment-indexed phenotype fitness.
-- This bridge says when a phenotype is realised as a focal player's strategy
-- inside an interaction profile and when the resulting game outcome maps to the
-- exact selection fitness.  Strategic preference is still not identified with
-- evolutionary fitness without a separate order alignment.
------------------------------------------------------------------------

record EvolutionaryStrategicRealisation
    (G : Game.StrategicGame)
    (E : Evolution.EvolutionarySystem) : Set₁ where
  constructor evolutionary-strategic-realisation
  field
    focalPlayer : Game.Player G
    environment : Evolution.EvolutionarySystem.Environment E

    phenotypeToStrategy :
      Evolution.EvolutionarySystem.Phenotype E →
      Game.Strategy G focalPlayer

    profileForPhenotype :
      Evolution.EvolutionarySystem.Phenotype E →
      Game.Profile G

    profileUsesPhenotypeStrategy :
      (phenotype : Evolution.EvolutionarySystem.Phenotype E) →
      Game.strategyAt G (profileForPhenotype phenotype) focalPlayer
      ≡ phenotypeToStrategy phenotype

    outcomeToFitness :
      Game.Outcome G → Evolution.EvolutionarySystem.Fitness E

    gameOutcomeMatchesSelection :
      (phenotype : Evolution.EvolutionarySystem.Phenotype E) →
      outcomeToFitness (Game.outcome G (profileForPhenotype phenotype))
      ≡ Evolution.EvolutionarySystem.select E environment phenotype

    realisationReference : String
    ecologicalContextReference : String

open EvolutionaryStrategicRealisation public

record EvolutionaryFitnessPreferenceAlignment
    {G : Game.StrategicGame}
    {E : Evolution.EvolutionarySystem}
    (R : EvolutionaryStrategicRealisation G E) : Set₁ where
  constructor evolutionary-fitness-preference-alignment
  field
    FitnessBetter :
      Evolution.EvolutionarySystem.Fitness E →
      Evolution.EvolutionarySystem.Fitness E → Set

    strictPreferenceImpliesFitnessBetter :
      (left right : Game.Outcome G) →
      Game.StrictlyPrefers G (focalPlayer R) left right →
      FitnessBetter
        (outcomeToFitness R left)
        (outcomeToFitness R right)

    alignmentReference : String

open EvolutionaryFitnessPreferenceAlignment public

------------------------------------------------------------------------
-- Selection and best response remain different operators.  The bridge gives a
-- same-object comparison surface but does not manufacture evolutionary stable
-- strategy, invasion fitness, fixation probability, replicator dynamics, or a
-- historical trajectory.
------------------------------------------------------------------------

record PhenotypeStrategicSelectionReceipt
    {G : Game.StrategicGame}
    {E : Evolution.EvolutionarySystem}
    (R : EvolutionaryStrategicRealisation G E) : Set₁ where
  constructor phenotype-strategic-selection-receipt
  field
    phenotype : Evolution.EvolutionarySystem.Phenotype E
    profile : Game.Profile G

    profileMatchesRealisation :
      profile ≡ profileForPhenotype R phenotype

    fitness : Evolution.EvolutionarySystem.Fitness E
    fitnessMatchesSelection :
      fitness ≡ Evolution.EvolutionarySystem.select E (environment R) phenotype

    strategyMatchesPhenotype :
      Game.strategyAt G profile (focalPlayer R)
      ≡ phenotypeToStrategy R phenotype

    receiptReference : String

open PhenotypeStrategicSelectionReceipt public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data FitnessMeansUtilityPermission : Set where

data UtilityMeansFitnessPermission : Set where

data NashMeansEvolutionarilyStablePermission : Set where

data BestResponseMeansSelectedPhenotypePermission : Set where

data EvolutionarySelectionMeansIndividualIntentPermission : Set where

data StrategicEquilibriumMeansHistoricalFixationPermission : Set where

data FitnessOrderingMeansMoralProgressPermission : Set where

fitnessDoesNotAutomaticallyBecomeUtility : FitnessMeansUtilityPermission → ⊥
fitnessDoesNotAutomaticallyBecomeUtility ()

utilityDoesNotAutomaticallyBecomeFitness : UtilityMeansFitnessPermission → ⊥
utilityDoesNotAutomaticallyBecomeFitness ()

nashDoesNotAutomaticallyBecomeESS : NashMeansEvolutionarilyStablePermission → ⊥
nashDoesNotAutomaticallyBecomeESS ()

bestResponseDoesNotAutomaticallyBecomeSelectedPhenotype :
  BestResponseMeansSelectedPhenotypePermission → ⊥
bestResponseDoesNotAutomaticallyBecomeSelectedPhenotype ()

selectionDoesNotBecomeIndividualIntent :
  EvolutionarySelectionMeansIndividualIntentPermission → ⊥
selectionDoesNotBecomeIndividualIntent ()

strategicEquilibriumDoesNotProveHistoricalFixation :
  StrategicEquilibriumMeansHistoricalFixationPermission → ⊥
strategicEquilibriumDoesNotProveHistoricalFixation ()

fitnessOrderingDoesNotBecomeMoralProgress :
  FitnessOrderingMeansMoralProgressPermission → ⊥
fitnessOrderingDoesNotBecomeMoralProgress ()

record EvolutionaryStrategicBoundary : Set where
  constructor evolutionary-strategic-boundary
  field
    phenotypeStrategyProjectionExplicit : Bool
    ecologicalContextExplicit : Bool
    gameOutcomeFitnessWeldExplicit : Bool
    preferenceFitnessAlignmentSeparate : Bool
    nashAutomaticallyMeansESS : Bool
    equilibriumAutomaticallyPredictsFixation : Bool

canonicalEvolutionaryStrategicBoundary : EvolutionaryStrategicBoundary
canonicalEvolutionaryStrategicBoundary =
  evolutionary-strategic-boundary true true true true false false
