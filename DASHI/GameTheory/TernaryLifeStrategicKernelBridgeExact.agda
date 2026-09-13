module DASHI.GameTheory.TernaryLifeStrategicKernelBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)

import DASHI.GameTheory.StrategicInteractionCoreExact as Game
import DASHI.Dynamics.TernaryLifeGame as Life

------------------------------------------------------------------------
-- LEGACY TERNARY-LIFE GAME -> CANONICAL STRATEGIC KERNEL
--
-- The older TernaryLifeGame already owns an executable local best-response
-- rule and proves that playing it yields `win`.  This module does not replace
-- that owner.  It realizes each fixed (rule, neighbourhood observation) as a
-- one-player normal-form game in the canonical strategic kernel.
------------------------------------------------------------------------

data LifeWeaklyPrefers : Life.Outcome → Life.Outcome → Set where
  winWeakWin : LifeWeaklyPrefers Life.win Life.win
  winWeakHold : LifeWeaklyPrefers Life.win Life.hold
  winWeakLoss : LifeWeaklyPrefers Life.win Life.loss
  holdWeakHold : LifeWeaklyPrefers Life.hold Life.hold
  holdWeakLoss : LifeWeaklyPrefers Life.hold Life.loss
  lossWeakLoss : LifeWeaklyPrefers Life.loss Life.loss

data LifeStrictlyPrefers : Life.Outcome → Life.Outcome → Set where
  winStrictHold : LifeStrictlyPrefers Life.win Life.hold
  winStrictLoss : LifeStrictlyPrefers Life.win Life.loss
  holdStrictLoss : LifeStrictlyPrefers Life.hold Life.loss

lifeStrictImpliesWeak :
  (better worse : Life.Outcome) →
  LifeStrictlyPrefers better worse →
  LifeWeaklyPrefers better worse
lifeStrictImpliesWeak .Life.win .Life.hold winStrictHold = winWeakHold
lifeStrictImpliesWeak .Life.win .Life.loss winStrictLoss = winWeakLoss
lifeStrictImpliesWeak .Life.hold .Life.loss holdStrictLoss = holdWeakLoss

lifeStrategicGame : Life.Rule → Life.Observation → Game.StrategicGame
lifeStrategicGame rule observation =
  Game.strategic-game
    ⊤
    Life.Strategy
    Life.Outcome
    (λ _ → Life.Strategy)
    (λ profile _ → profile)
    (λ _ _ alternative → alternative)
    (λ _ _ _ → refl)
    (Life.localPayoff rule observation)
    (λ _ → LifeWeaklyPrefers)
    (λ _ → LifeStrictlyPrefers)
    (λ _ better worse → lifeStrictImpliesWeak better worse)
    "legacy ternary-Life local three-strategy game realized as one-player canonical strategic game"
    "loss/hold/win local-rule outcome"
    "win > hold > loss ordinal preference; distinct from biological fitness or truth"

nothingStrictlyBetterThanWin :
  (outcome : Life.Outcome) →
  LifeStrictlyPrefers outcome Life.win → ⊥
nothingStrictlyBetterThanWin Life.loss ()
nothingStrictlyBetterThanWin Life.hold ()
nothingStrictlyBetterThanWin Life.win ()

lifeBestResponseIsNash :
  (rule : Life.Rule) →
  (observation : Life.Observation) →
  Game.NashEquilibrium (lifeStrategicGame rule observation)
lifeBestResponseIsNash rule observation =
  Game.nash-equilibrium
    (Life.bestResponse rule observation)
    everyPlayerBestResponds
  where
    everyPlayerBestResponds :
      (player : Game.Player (lifeStrategicGame rule observation)) →
      Game.BestResponseAt
        (lifeStrategicGame rule observation)
        (Life.bestResponse rule observation)
        player
    everyPlayerBestResponds tt alternative profitable
      rewrite Life.selfPayoff rule observation =
        nothingStrictlyBetterThanWin
          (Life.localPayoff rule observation alternative)
          profitable

classicLocalNash :
  (observation : Life.Observation) →
  Game.NashEquilibrium (lifeStrategicGame Life.classicRule observation)
classicLocalNash = lifeBestResponseIsNash Life.classicRule

------------------------------------------------------------------------
-- Boundaries: this is a local single-site fixture, not a theorem about global
-- cellular-automaton equilibrium, spatial Nash, evolutionary stability, or the
-- learned Python simulator.
------------------------------------------------------------------------

data LocalBestResponseMeansGlobalSpatialNashPermission : Set where

data LocalNashMeansCellularAutomatonFixedPointPermission : Set where

data LocalNashMeansEvolutionaryStabilityPermission : Set where

data LocalPayoffMeansBiologicalFitnessPermission : Set where

data LearnedRuleMeansCanonicalRulePermission : Set where

localBestResponseDoesNotProveGlobalSpatialNash :
  LocalBestResponseMeansGlobalSpatialNashPermission → ⊥
localBestResponseDoesNotProveGlobalSpatialNash ()

localNashDoesNotProveCAFixedPoint :
  LocalNashMeansCellularAutomatonFixedPointPermission → ⊥
localNashDoesNotProveCAFixedPoint ()

localNashDoesNotProveESS : LocalNashMeansEvolutionaryStabilityPermission → ⊥
localNashDoesNotProveESS ()

localPayoffDoesNotBecomeFitness : LocalPayoffMeansBiologicalFitnessPermission → ⊥
localPayoffDoesNotBecomeFitness ()

learnedRuleDoesNotBecomeCanonicalRule : LearnedRuleMeansCanonicalRulePermission → ⊥
learnedRuleDoesNotBecomeCanonicalRule ()

record TernaryLifeStrategicBridgeBoundary : Set where
  constructor ternary-life-strategic-bridge-boundary
  field
    legacyRuleReused : Bool
    legacyBestResponseReused : Bool
    localPureNashProved : Bool
    globalSpatialNashProved : Bool
    cellularFixedPointProved : Bool
    evolutionaryStabilityProved : Bool

canonicalTernaryLifeStrategicBridgeBoundary : TernaryLifeStrategicBridgeBoundary
canonicalTernaryLifeStrategicBridgeBoundary =
  ternary-life-strategic-bridge-boundary true true true false false false
