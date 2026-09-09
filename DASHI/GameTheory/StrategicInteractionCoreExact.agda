module DASHI.GameTheory.StrategicInteractionCoreExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- STRATEGIC INTERACTION CORE
--
-- Ordinal/player-relative preference is primitive.  Numerical utility, reward,
-- fitness, defect, evidence, welfare and moral value are separate downstream
-- realisations and are not identified here.
------------------------------------------------------------------------

record StrategicGame : Set₁ where
  constructor strategic-game
  field
    Player Profile Outcome : Set
    Strategy : Player → Set

    strategyAt : (profile : Profile) → (player : Player) → Strategy player

    deviate :
      (profile : Profile) →
      (player : Player) →
      Strategy player →
      Profile

    deviationInstalls :
      (profile : Profile) →
      (player : Player) →
      (strategy : Strategy player) →
      strategyAt (deviate profile player strategy) player ≡ strategy

    outcome : Profile → Outcome

    WeaklyPrefers : Player → Outcome → Outcome → Set
    StrictlyPrefers : Player → Outcome → Outcome → Set

    strictImpliesWeak :
      (player : Player) →
      (better worse : Outcome) →
      StrictlyPrefers player better worse →
      WeaklyPrefers player better worse

    gameReference : String
    outcomeReference : String
    preferenceReference : String

open StrategicGame public

deviationOutcome :
  (G : StrategicGame) →
  (profile : Profile G) →
  (player : Player G) →
  Strategy G player →
  Outcome G
deviationOutcome G profile player strategy =
  outcome G (deviate G profile player strategy)

ProfitableDeviation :
  (G : StrategicGame) →
  (profile : Profile G) →
  (player : Player G) →
  Strategy G player →
  Set
ProfitableDeviation G profile player alternative =
  StrictlyPrefers G player
    (deviationOutcome G profile player alternative)
    (outcome G profile)

BestResponseAt :
  (G : StrategicGame) →
  Profile G →
  Player G →
  Set
BestResponseAt G profile player =
  (alternative : Strategy G player) →
  ProfitableDeviation G profile player alternative →
  ⊥

record NashEquilibrium (G : StrategicGame) : Set₁ where
  constructor nash-equilibrium
  field
    profile : Profile G
    everyPlayerBestResponds :
      (player : Player G) →
      BestResponseAt G profile player

open NashEquilibrium public

nashBlocksProfitableUnilateralDeviation :
  ∀ {G : StrategicGame} →
  (N : NashEquilibrium G) →
  (player : Player G) →
  (alternative : Strategy G player) →
  ProfitableDeviation G (profile N) player alternative →
  ⊥
nashBlocksProfitableUnilateralDeviation N player alternative =
  everyPlayerBestResponds N player alternative

------------------------------------------------------------------------
-- Dominance and Pareto comparison remain separate from Nash equilibrium.
------------------------------------------------------------------------

WeaklyDominatesAt :
  (G : StrategicGame) →
  (player : Player G) →
  Strategy G player →
  Strategy G player →
  Profile G →
  Set
WeaklyDominatesAt G player candidate alternative context =
  WeaklyPrefers G player
    (outcome G (deviate G context player candidate))
    (outcome G (deviate G context player alternative))

DominantStrategy :
  (G : StrategicGame) →
  (player : Player G) →
  Strategy G player →
  Set
DominantStrategy G player candidate =
  (context : Profile G) →
  (alternative : Strategy G player) →
  WeaklyDominatesAt G player candidate alternative context

ParetoWeaklyImproves :
  (G : StrategicGame) →
  Profile G →
  Profile G →
  Set
ParetoWeaklyImproves G before after =
  (player : Player G) →
  WeaklyPrefers G player (outcome G after) (outcome G before)

record ParetoImprovement
    (G : StrategicGame)
    (before after : Profile G) : Set₁ where
  constructor pareto-improvement
  field
    weaklyImprovesEveryone : ParetoWeaklyImproves G before after
    strictlyImprovedPlayer : Player G
    strictlyImprovesOne :
      StrictlyPrefers G strictlyImprovedPlayer
        (outcome G after)
        (outcome G before)

open ParetoImprovement public

------------------------------------------------------------------------
-- Optional numerical payoff realisation.  Payoff preserves the declared
-- ordinal preference only when an explicit order-realisation receipt is paid.
------------------------------------------------------------------------

record NumericalPayoffRealisation (G : StrategicGame) : Set₁ where
  constructor numerical-payoff-realisation
  field
    Payoff : Set
    _≤P_ : Payoff → Payoff → Set
    _<P_ : Payoff → Payoff → Set

    payoff : Player G → Outcome G → Payoff

    weakPreferenceRealised :
      (player : Player G) →
      (left right : Outcome G) →
      WeaklyPrefers G player left right →
      _≤P_ (payoff player right) (payoff player left)

    strictPreferenceRealised :
      (player : Player G) →
      (left right : Outcome G) →
      StrictlyPrefers G player left right →
      _<P_ (payoff player right) (payoff player left)

    payoffReference : String
    orderReference : String

open NumericalPayoffRealisation public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data NashMeansParetoOptimalPermission : Set where

data NashMeansSociallyOptimalPermission : Set where

data PreferenceMeansNumericalUtilityPermission : Set where

data PayoffMeansEvolutionaryFitnessPermission : Set where

data PayoffMeansAgenticDefectPermission : Set where

data PayoffMeansStatisticalEvidencePermission : Set where

data PayoffMeansMoralValuePermission : Set where

data BestResponseMeansTruthPermission : Set where

data EquilibriumMeansHistoricalPredictionPermission : Set where

data UnilateralStabilityMeansCoalitionalStabilityPermission : Set where

nashDoesNotAutomaticallyMeanParetoOptimal :
  NashMeansParetoOptimalPermission → ⊥
nashDoesNotAutomaticallyMeanParetoOptimal ()

nashDoesNotAutomaticallyMeanSociallyOptimal :
  NashMeansSociallyOptimalPermission → ⊥
nashDoesNotAutomaticallyMeanSociallyOptimal ()

preferenceDoesNotManufactureNumericalUtility :
  PreferenceMeansNumericalUtilityPermission → ⊥
preferenceDoesNotManufactureNumericalUtility ()

payoffDoesNotAutomaticallyBecomeFitness :
  PayoffMeansEvolutionaryFitnessPermission → ⊥
payoffDoesNotAutomaticallyBecomeFitness ()

payoffDoesNotAutomaticallyBecomeAgenticDefect :
  PayoffMeansAgenticDefectPermission → ⊥
payoffDoesNotAutomaticallyBecomeAgenticDefect ()

payoffDoesNotAutomaticallyBecomeStatisticalEvidence :
  PayoffMeansStatisticalEvidencePermission → ⊥
payoffDoesNotAutomaticallyBecomeStatisticalEvidence ()

payoffDoesNotAutomaticallyBecomeMoralValue :
  PayoffMeansMoralValuePermission → ⊥
payoffDoesNotAutomaticallyBecomeMoralValue ()

bestResponseDoesNotManufactureTruth :
  BestResponseMeansTruthPermission → ⊥
bestResponseDoesNotManufactureTruth ()

equilibriumDoesNotByItselfPredictHistory :
  EquilibriumMeansHistoricalPredictionPermission → ⊥
equilibriumDoesNotByItselfPredictHistory ()

nashDoesNotAutomaticallyGiveCoalitionalStability :
  UnilateralStabilityMeansCoalitionalStabilityPermission → ⊥
nashDoesNotAutomaticallyGiveCoalitionalStability ()

record StrategicInteractionBoundary : Set where
  constructor strategic-interaction-boundary
  field
    preferenceIsPlayerRelative : Bool
    unilateralDeviationExplicit : Bool
    nashIsNoProfitableUnilateralDeviation : Bool
    dominanceSeparateFromNash : Bool
    paretoSeparateFromNash : Bool
    numericalPayoffOptional : Bool
    utilityFitnessDefectEvidenceSeparated : Bool
    equilibriumAutomaticallyPredictsHistory : Bool

canonicalStrategicInteractionBoundary : StrategicInteractionBoundary
canonicalStrategicInteractionBoundary =
  strategic-interaction-boundary
    true true true true true true true false
