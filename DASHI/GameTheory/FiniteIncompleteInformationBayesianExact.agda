module DASHI.GameTheory.FiniteIncompleteInformationBayesianExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_)

import DASHI.GameTheory.StrategicInteractionCoreExact as Game
import DASHI.GameTheory.FiniteMixedStrategyExpectedUtilityExact as Mixed
import DASHI.Cognition.PNF.GenericExpectedFibreRateExact as Expected
import DASHI.Cognition.PNF.MemoryFibre as Memory

------------------------------------------------------------------------
-- FINITE INCOMPLETE-INFORMATION / BAYESIAN GAMES
--
-- This is a bounded common-prior realization.  Uncertainty about the world is
-- distinct from randomisation over actions.  A contingent strategy is a map
-- from the player's information signal/type to a pure strategy.  The world
-- prior is an exact finite rational law.  No sigma-algebra, posterior theorem,
-- Harsanyi type hierarchy, or infinite common knowledge is invented here.
------------------------------------------------------------------------

record WeightedWorld (World : Set) : Set where
  constructor weighted-world
  field
    probability : Expected.ProbabilityAtom
    world : World

open WeightedWorld public

worldMass : ∀ {World} → WeightedWorld World → ℚ
worldMass atom = Expected.probabilityMass (probability atom)

finiteWorldMass : ∀ {World} → List (WeightedWorld World) → ℚ
finiteWorldMass [] = 0ℚ
finiteWorldMass (atom ∷ atoms) = worldMass atom + finiteWorldMass atoms

record NormalizedFiniteWorldPrior (World : Set) : Set₁ where
  constructor normalized-finite-world-prior
  field
    atoms : List (WeightedWorld World)
    normalized : finiteWorldMass atoms ≡ 1ℚ
    priorReference : String

open NormalizedFiniteWorldPrior public

record FiniteBayesianGame (G : Game.StrategicGame) : Set₁ where
  constructor finite-bayesian-game
  field
    World : Set
    Signal : Game.Player G → Set

    signalAt :
      (world : World) →
      (player : Game.Player G) →
      Signal player

    PlanProfile : Set

    contingentStrategyAt :
      (plans : PlanProfile) →
      (player : Game.Player G) →
      Signal player →
      Game.Strategy G player

    realiseProfile : PlanProfile → World → Game.Profile G

    realisedStrategyMatchesSignal :
      (plans : PlanProfile) →
      (world : World) →
      (player : Game.Player G) →
      Game.strategyAt G (realiseProfile plans world) player
      ≡ contingentStrategyAt plans player (signalAt world player)

    deviatePlan :
      (plans : PlanProfile) →
      (player : Game.Player G) →
      (Signal player → Game.Strategy G player) →
      PlanProfile

    deviatingPlanInstalled :
      (plans : PlanProfile) →
      (player : Game.Player G) →
      (alternative : Signal player → Game.Strategy G player) →
      (signal : Signal player) →
      contingentStrategyAt (deviatePlan plans player alternative) player signal
      ≡ alternative signal

    DifferentPlayer : Game.Player G → Game.Player G → Set

    OtherPlayerPlanUnchanged :
      PlanProfile → PlanProfile → Game.Player G → Set

    deviationLeavesOtherPlayersUnchanged :
      (plans : PlanProfile) →
      (player : Game.Player G) →
      (alternative : Signal player → Game.Strategy G player) →
      (other : Game.Player G) →
      DifferentPlayer player other →
      OtherPlayerPlanUnchanged
        plans
        (deviatePlan plans player alternative)
        other

    outcomeAt : World → Game.Profile G → Game.Outcome G
    prior : NormalizedFiniteWorldPrior World

    informationReference : String
    planReference : String
    outcomeReference : String

open FiniteBayesianGame public

------------------------------------------------------------------------
-- Expected utility under the finite common prior.
------------------------------------------------------------------------

worldExpectedUtility :
  ∀ {G}
    (B : FiniteBayesianGame G) →
  Mixed.FiniteExpectedUtilitySurface G →
  Game.Player G →
  PlanProfile B →
  List (WeightedWorld (World B)) → ℚ
worldExpectedUtility B U player plans [] = 0ℚ
worldExpectedUtility {G} B U player plans (atom ∷ atoms) =
  worldMass atom
    * Mixed.payoffToRational U
        (Game.payoff (Mixed.numericalPayoff U) player
          (outcomeAt B (world atom)
            (realiseProfile B plans (world atom))))
  + worldExpectedUtility B U player plans atoms

BayesianBestResponseAt :
  ∀ {G}
    (B : FiniteBayesianGame G) →
  (U : Mixed.FiniteExpectedUtilitySurface G) →
  PlanProfile B →
  Game.Player G → Set₁
BayesianBestResponseAt {G} B U plans player =
  (alternative : Signal B player → Game.Strategy G player) →
  worldExpectedUtility B U player
    (deviatePlan B plans player alternative)
    (NormalizedFiniteWorldPrior.atoms (prior B))
  ≤
  worldExpectedUtility B U player plans
    (NormalizedFiniteWorldPrior.atoms (prior B))

record FiniteBayesianNashEquilibrium
    (G : Game.StrategicGame)
    (B : FiniteBayesianGame G)
    (U : Mixed.FiniteExpectedUtilitySurface G) : Set₁ where
  constructor finite-bayesian-nash-equilibrium
  field
    plans : PlanProfile B
    everyPlayerBayesianBestResponds :
      (player : Game.Player G) →
      BayesianBestResponseAt B U plans player

    equilibriumReference : String

open FiniteBayesianNashEquilibrium public

------------------------------------------------------------------------
-- Optional cognitive interpretation.  A bounded-common-belief object may be
-- associated with the information model, but it is not definitionally the
-- finite Bayesian prior and explicitly does not assert infinite common
-- knowledge.
------------------------------------------------------------------------

record BoundedBeliefBayesianInterpretation
    {G : Game.StrategicGame}
    (B : FiniteBayesianGame G) : Set₁ where
  constructor bounded-belief-bayesian-interpretation
  field
    boundedBelief : Memory.BoundedCommonBelief
    BeliefRealisesInformationModel : Set
    beliefRealisationReceipt : BeliefRealisesInformationModel
    interpretationReference : String

open BoundedBeliefBayesianInterpretation public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data MixedStrategyMeansWorldUncertaintyPermission : Set where

data WorldPriorMeansEmpiricalFrequencyPermission : Set where

data SignalMeansTrueWorldKnownPermission : Set where

data BayesianBestResponseMeansPosteriorBayesRulePermission : Set where

data BoundedCommonBeliefMeansInfiniteCommonKnowledgePermission : Set where

data BayesianNashMeansPureNashPermission : Set where

data BayesianNashMeansHistoricalPredictionPermission : Set where

data PriorMeansTruthAuthorityPermission : Set where

mixedActionRandomisationIsNotWorldUncertainty :
  MixedStrategyMeansWorldUncertaintyPermission → ⊥
mixedActionRandomisationIsNotWorldUncertainty ()

priorDoesNotAutomaticallyEqualObservedFrequency :
  WorldPriorMeansEmpiricalFrequencyPermission → ⊥
priorDoesNotAutomaticallyEqualObservedFrequency ()

signalDoesNotAutomaticallyRevealTrueWorld :
  SignalMeansTrueWorldKnownPermission → ⊥
signalDoesNotAutomaticallyRevealTrueWorld ()

bayesianBestResponseDoesNotInventPosteriorUpdate :
  BayesianBestResponseMeansPosteriorBayesRulePermission → ⊥
bayesianBestResponseDoesNotInventPosteriorUpdate ()

boundedBeliefDoesNotBecomeInfiniteCommonKnowledge :
  BoundedCommonBeliefMeansInfiniteCommonKnowledgePermission → ⊥
boundedBeliefDoesNotBecomeInfiniteCommonKnowledge ()

bayesianNashDoesNotCollapseToPureNash : BayesianNashMeansPureNashPermission → ⊥
bayesianNashDoesNotCollapseToPureNash ()

bayesianNashDoesNotPredictHistoricalPlay :
  BayesianNashMeansHistoricalPredictionPermission → ⊥
bayesianNashDoesNotPredictHistoricalPlay ()

priorDoesNotCreateTruthAuthority : PriorMeansTruthAuthorityPermission → ⊥
priorDoesNotCreateTruthAuthority ()

record FiniteBayesianGameBoundary : Set where
  constructor finite-bayesian-game-boundary
  field
    finiteWorldPriorExplicit : Bool
    worldUncertaintySeparatedFromActionRandomisation : Bool
    playerSignalExplicit : Bool
    contingentStrategyExplicit : Bool
    unilateralPlanDeviationExplicit : Bool
    finitePriorExpectedUtilityExplicit : Bool
    boundedBeliefInterpretationOptional : Bool
    posteriorUpdatingInventedHere : Bool
    infiniteCommonKnowledgeInventedHere : Bool

canonicalFiniteBayesianGameBoundary : FiniteBayesianGameBoundary
canonicalFiniteBayesianGameBoundary =
  finite-bayesian-game-boundary
    true true true true true true true false false
