module DASHI.GameTheory.SymmetricEvolutionaryStableStrategyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.GameTheory.EvolutionaryInvasionStabilityExact as Invasion
import DASHI.GameTheory.GameTheorySourceAtlasExact as Sources

------------------------------------------------------------------------
-- CLASSIC SYMMETRIC ESS CRITERION
--
-- For every distinct mutant t, resident s is protected either because s does
-- strictly better against s than t does against s, or because they tie against
-- s and s does strictly better against t than t does against itself.
--
-- This is a source-aligned theorem shape inspired by Maynard Smith--Price.  It
-- is not identified with arbitrary population-context invasion stability until
-- an application supplies a bridge between pairwise fitness and its population
-- fitness carrier.
------------------------------------------------------------------------

record SymmetricEvolutionaryGame : Set₁ where
  constructor symmetric-evolutionary-game
  field
    Strategy Fitness : Set

    fitnessAgainst : Strategy → Strategy → Fitness

    _>F_ : Fitness → Fitness → Set
    _≈F_ : Fitness → Fitness → Set

    StrategyDifferent : Strategy → Strategy → Set

    gameReference : String
    fitnessReference : String
    sourceReference : String

open SymmetricEvolutionaryGame public

record EvolutionarilyStableStrategy
    (G : SymmetricEvolutionaryGame) : Set₁ where
  constructor evolutionarily-stable-strategy
  field
    resident : Strategy G

    invasionCriterion :
      (mutant : Strategy G) →
      StrategyDifferent G mutant resident →
      (
        _>F_ G
          (fitnessAgainst G resident resident)
          (fitnessAgainst G mutant resident)
      )
      ⊎
      (
        _≈F_ G
          (fitnessAgainst G resident resident)
          (fitnessAgainst G mutant resident)
        ×
        _>F_ G
          (fitnessAgainst G resident mutant)
          (fitnessAgainst G mutant mutant)
      )

    essReference : String

open EvolutionarilyStableStrategy public

------------------------------------------------------------------------
-- Conditional bridge to the broader population-context invasion carrier.
------------------------------------------------------------------------

record ESSInvasionBridge
    {G : SymmetricEvolutionaryGame}
    (stable : EvolutionarilyStableStrategy G) : Set₁ where
  constructor ess-invasion-bridge
  field
    PopulationContext : Set
    RareMutantContext : Strategy G → PopulationContext → Set

    FitnessInContext : PopulationContext → Strategy G → Fitness G

    pairwiseCriterionBlocksContextAdvantage :
      (mutant : Strategy G) →
      StrategyDifferent G mutant (resident stable) →
      (context : PopulationContext) →
      RareMutantContext mutant context →
      _>F_ G
        (FitnessInContext context mutant)
        (FitnessInContext context (resident stable)) →
      ⊥

    bridgeReference : String

open ESSInvasionBridge public

essBlocksReceiptedContextualInvasion :
  ∀ {G stable}
    (B : ESSInvasionBridge {G} stable) →
  (mutant : Strategy G) →
  StrategyDifferent G mutant (resident stable) →
  (context : PopulationContext B) →
  RareMutantContext B mutant context →
  _>F_ G
    (FitnessInContext B context mutant)
    (FitnessInContext B context (resident stable)) →
  ⊥
essBlocksReceiptedContextualInvasion B mutant different context rare advantage =
  pairwiseCriterionBlocksContextAdvantage B mutant different context rare advantage

------------------------------------------------------------------------
-- Attribution compatibility.
------------------------------------------------------------------------

sourceAtlasBoundary : Sources.canonicalGameTheorySourceCount ≡ 8
sourceAtlasBoundary = Sources.canonicalGameTheorySourceCountIsEight

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ESSMeansNashPermission : Set where

data NashMeansESSPermission : Set where

data ESSMeansFixationPermission : Set where

data PairwiseESSMeansArbitraryPopulationStabilityPermission : Set where

data ESSMeansGlobalFitnessMaximumPermission : Set where

data ESSMeansMoralValuePermission : Set where

classicESSDoesNotCollapseToNormalFormNash : ESSMeansNashPermission → ⊥
classicESSDoesNotCollapseToNormalFormNash ()

normalFormNashDoesNotCollapseToESS : NashMeansESSPermission → ⊥
normalFormNashDoesNotCollapseToESS ()

classicESSDoesNotProveFixation : ESSMeansFixationPermission → ⊥
classicESSDoesNotProveFixation ()

pairwiseESSNeedsBridgeForPopulationContext :
  PairwiseESSMeansArbitraryPopulationStabilityPermission → ⊥
pairwiseESSNeedsBridgeForPopulationContext ()

classicESSDoesNotProveGlobalFitnessMaximum :
  ESSMeansGlobalFitnessMaximumPermission → ⊥
classicESSDoesNotProveGlobalFitnessMaximum ()

classicESSDoesNotCreateMoralValue : ESSMeansMoralValuePermission → ⊥
classicESSDoesNotCreateMoralValue ()

record SymmetricESSBoundary : Set where
  constructor symmetric-ess-boundary
  field
    pairwiseFitnessExplicit : Bool
    firstESSClauseExplicit : Bool
    tieBreakerESSClauseExplicit : Bool
    mutantDifferenceExplicit : Bool
    populationContextBridgeSeparate : Bool
    fixationAutomatic : Bool
    moralValueAutomatic : Bool

canonicalSymmetricESSBoundary : SymmetricESSBoundary
canonicalSymmetricESSBoundary =
  symmetric-ess-boundary true true true true true false false
