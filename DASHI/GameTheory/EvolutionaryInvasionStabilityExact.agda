module DASHI.GameTheory.EvolutionaryInvasionStabilityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.GameTheory.StrategicInteractionCoreExact as Strategic
import DASHI.GameTheory.EvolutionaryStrategicSelectionBridgeExact as EvolutionBridge
import DASHI.Biology.Evolution.EvolutionaryPopulationDynamics as Evolution

------------------------------------------------------------------------
-- EVOLUTIONARY INVASION / STABILITY
--
-- Nash is unilateral strategic stability at a profile.  Evolutionary invasion
-- stability is population-contextual: a rare alternative must fail to obtain a
-- fitness advantage against the resident context.  Fixation and long-run
-- population dynamics are still separate historical/dynamical questions.
------------------------------------------------------------------------

record EvolutionaryInvasionSurface
    (G : Strategic.StrategicGame)
    (E : Evolution.EvolutionarySystem)
    (R : EvolutionBridge.EvolutionaryStrategicRealisation G E) : Set₁ where
  constructor evolutionary-invasion-surface
  field
    PopulationContext : Set

    residentContext : PopulationContext

    contextEnvironment :
      PopulationContext →
      Evolution.EvolutionarySystem.Environment E

    profileInContext :
      PopulationContext →
      Evolution.EvolutionarySystem.Phenotype E →
      Strategic.Profile G

    profileUsesPhenotypeStrategy :
      (context : PopulationContext) →
      (phenotype : Evolution.EvolutionarySystem.Phenotype E) →
      Strategic.strategyAt G
        (profileInContext context phenotype)
        (EvolutionBridge.focalPlayer R)
      ≡ EvolutionBridge.phenotypeToStrategy R phenotype

    fitnessInContext :
      PopulationContext →
      Evolution.EvolutionarySystem.Phenotype E →
      Evolution.EvolutionarySystem.Fitness E

    fitnessMatchesSelection :
      (context : PopulationContext) →
      (phenotype : Evolution.EvolutionarySystem.Phenotype E) →
      fitnessInContext context phenotype
      ≡ Evolution.EvolutionarySystem.select E
          (contextEnvironment context)
          phenotype

    RareInvasion :
      (resident mutant : Evolution.EvolutionarySystem.Phenotype E) →
      PopulationContext → Set

    FitnessBetter :
      Evolution.EvolutionarySystem.Fitness E →
      Evolution.EvolutionarySystem.Fitness E → Set

    contextReference : String
    invasionReference : String
    fitnessReference : String

open EvolutionaryInvasionSurface public

MutantInvades :
  ∀ {G E R} →
  (S : EvolutionaryInvasionSurface G E R) →
  (resident mutant : Evolution.EvolutionarySystem.Phenotype E) →
  PopulationContext S → Set
MutantInvades S resident mutant context =
  RareInvasion S resident mutant context
  ×
  FitnessBetter S
    (fitnessInContext S context mutant)
    (fitnessInContext S context resident)

record EvolutionaryInvasionStability
    {G : Strategic.StrategicGame}
    {E : Evolution.EvolutionarySystem}
    {R : EvolutionBridge.EvolutionaryStrategicRealisation G E}
    (S : EvolutionaryInvasionSurface G E R) : Set₁ where
  constructor evolutionary-invasion-stability
  field
    resident : Evolution.EvolutionarySystem.Phenotype E

    noRareMutantFitnessAdvantage :
      (mutant : Evolution.EvolutionarySystem.Phenotype E) →
      (context : PopulationContext S) →
      RareInvasion S resident mutant context →
      FitnessBetter S
        (fitnessInContext S context mutant)
        (fitnessInContext S context resident) →
      ⊥

    stabilityReference : String

open EvolutionaryInvasionStability public

stabilityBlocksInvasion :
  ∀ {G E R S}
    (stable : EvolutionaryInvasionStability {G} {E} {R} S) →
  (mutant : Evolution.EvolutionarySystem.Phenotype E) →
  (context : PopulationContext S) →
  MutantInvades S (resident stable) mutant context →
  ⊥
stabilityBlocksInvasion stable mutant context invasion =
  noRareMutantFitnessAdvantage stable mutant context
    (proj₁ invasion)
    (proj₂ invasion)

------------------------------------------------------------------------
-- Historical fixation remains separately receipted.
------------------------------------------------------------------------

record FixationReceipt
    {G : Strategic.StrategicGame}
    {E : Evolution.EvolutionarySystem}
    {R : EvolutionBridge.EvolutionaryStrategicRealisation G E}
    (S : EvolutionaryInvasionSurface G E R)
    (phenotype : Evolution.EvolutionarySystem.Phenotype E) : Set₁ where
  constructor fixation-receipt
  field
    Generation : Set
    initial final : Generation
    Later : Generation → Generation → Set
    finalLater : Later initial final

    PopulationFrequency : Set
    frequencyAt : Generation → Evolution.EvolutionarySystem.Phenotype E → PopulationFrequency
    Fixed : PopulationFrequency → Set
    fixedAtFinal : Fixed (frequencyAt final phenotype)

    trajectoryReference : String
    fixationReference : String

open FixationReceipt public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data NashMeansInvasionStabilityPermission : Set where

data InvasionStabilityMeansFixationPermission : Set where

data FitnessAdvantageMeansCertainFixationPermission : Set where

data RareInvasionMeansMutationObservedPermission : Set where

data ESSMeansMoralSuperiorityPermission : Set where

data FixationMeansGlobalOptimalityPermission : Set where

nashDoesNotAutomaticallyGiveInvasionStability :
  NashMeansInvasionStabilityPermission → ⊥
nashDoesNotAutomaticallyGiveInvasionStability ()

invasionStabilityDoesNotProveHistoricalFixation :
  InvasionStabilityMeansFixationPermission → ⊥
invasionStabilityDoesNotProveHistoricalFixation ()

fitnessAdvantageDoesNotMakeFixationCertain :
  FitnessAdvantageMeansCertainFixationPermission → ⊥
fitnessAdvantageDoesNotMakeFixationCertain ()

rareInvasionModelDoesNotProveMutationObserved :
  RareInvasionMeansMutationObservedPermission → ⊥
rareInvasionModelDoesNotProveMutationObserved ()

evolutionaryStabilityDoesNotBecomeMoralSuperiority :
  ESSMeansMoralSuperiorityPermission → ⊥
evolutionaryStabilityDoesNotBecomeMoralSuperiority ()

fixationDoesNotProveGlobalOptimality :
  FixationMeansGlobalOptimalityPermission → ⊥
fixationDoesNotProveGlobalOptimality ()

record EvolutionaryInvasionBoundary : Set where
  constructor evolutionary-invasion-boundary
  field
    populationContextExplicit : Bool
    rareInvasionExplicit : Bool
    fitnessUsesEvolutionarySelection : Bool
    invasionStabilitySeparateFromNash : Bool
    fixationSeparateFromInvasionStability : Bool
    fitnessAdvantageAutomaticallyFixes : Bool

canonicalEvolutionaryInvasionBoundary : EvolutionaryInvasionBoundary
canonicalEvolutionaryInvasionBoundary =
  evolutionary-invasion-boundary true true true true true false
