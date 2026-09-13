module DASHI.GameTheory.SequentialExtensiveFormExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.GameTheory.StrategicInteractionCoreExact as Strategic

------------------------------------------------------------------------
-- SEQUENTIAL / EXTENSIVE-FORM STRATEGIC CORE
--
-- This owner adds history-sensitive continuation play without replacing the
-- normal-form StrategicGame.  Histories, reachable continuation nodes and
-- local deviations are explicit.  A normal-form Nash receipt does not imply
-- sequential rationality or subgame perfection.
------------------------------------------------------------------------

record ExtensiveStrategicGame : Set₁ where
  constructor extensive-strategic-game
  field
    Player Node History Outcome PlanProfile : Set
    Action : Node → Set

    root : Node
    initialHistory : History
    currentNode : History → Node
    initialAtRoot : currentNode initialHistory ≡ root

    mover : Node → Player
    extend :
      (history : History) →
      Action (currentNode history) →
      History

    nextNode :
      (node : Node) →
      Action node →
      Node

    extensionMovesNode :
      (history : History) →
      (action : Action (currentNode history)) →
      currentNode (extend history action)
      ≡ nextNode (currentNode history) action

    Terminal : Node → Set
    terminalOutcome :
      (node : Node) →
      Terminal node →
      Outcome

    continuationOutcome :
      History →
      PlanProfile →
      Outcome

    ReachableUnder : PlanProfile → History → Set

    ActionPlan : Player → Set
    actionAtHistory :
      (plans : PlanProfile) →
      (player : Player) →
      ActionPlan player

    deviationAtHistory :
      (plans : PlanProfile) →
      (history : History) →
      (alternative : ActionPlan (mover (currentNode history))) →
      PlanProfile

    deviationInstallsAtHistory :
      (plans : PlanProfile) →
      (history : History) →
      (alternative : ActionPlan (mover (currentNode history))) →
      actionAtHistory
        (deviationAtHistory plans history alternative)
        (mover (currentNode history))
      ≡ alternative

    WeaklyPrefers : Player → Outcome → Outcome → Set
    StrictlyPrefers : Player → Outcome → Outcome → Set

    strictImpliesWeak :
      (player : Player) →
      (better worse : Outcome) →
      StrictlyPrefers player better worse →
      WeaklyPrefers player better worse

    gameReference : String
    historyReference : String
    sequentialPreferenceReference : String

open ExtensiveStrategicGame public

SequentialProfitableDeviationAt :
  (G : ExtensiveStrategicGame) →
  (plans : PlanProfile G) →
  (history : History G) →
  ActionPlan G (mover G (currentNode G history)) →
  Set
SequentialProfitableDeviationAt G plans history alternative =
  StrictlyPrefers G
    (mover G (currentNode G history))
    (continuationOutcome G history
      (deviationAtHistory G plans history alternative))
    (continuationOutcome G history plans)

SequentialBestResponseAt :
  (G : ExtensiveStrategicGame) →
  (plans : PlanProfile G) →
  (history : History G) →
  Set₁
SequentialBestResponseAt G plans history =
  (alternative : ActionPlan G (mover G (currentNode G history))) →
  SequentialProfitableDeviationAt G plans history alternative →
  ⊥

record SequentialRationality
    (G : ExtensiveStrategicGame)
    (plans : PlanProfile G) : Set₁ where
  constructor sequential-rationality
  field
    everyReachableContinuationBestResponds :
      (history : History G) →
      ReachableUnder G plans history →
      SequentialBestResponseAt G plans history

    sequentialReference : String

open SequentialRationality public

record SubgamePerfectEquilibrium
    (G : ExtensiveStrategicGame) : Set₁ where
  constructor subgame-perfect-equilibrium
  field
    plans : PlanProfile G

    SubgameRoot : History G → Set

    everySubgameRootSequentiallyRational :
      (history : History G) →
      SubgameRoot history →
      SequentialBestResponseAt G plans history

    subgameReference : String

open SubgamePerfectEquilibrium public

subgamePerfectBlocksProfitableDeviationAtSubgameRoot :
  ∀ {G : ExtensiveStrategicGame} →
  (S : SubgamePerfectEquilibrium G) →
  (history : History G) →
  SubgameRoot S history →
  (alternative : ActionPlan G (mover G (currentNode G history))) →
  SequentialProfitableDeviationAt G (plans S) history alternative →
  ⊥
subgamePerfectBlocksProfitableDeviationAtSubgameRoot S history rootWitness alternative =
  everySubgameRootSequentiallyRational S history rootWitness alternative

------------------------------------------------------------------------
-- Optional normal-form realisation.  This is a bridge, not an identification.
------------------------------------------------------------------------

record NormalFormRealisation
    (E : ExtensiveStrategicGame)
    (N : Strategic.StrategicGame) : Set₁ where
  constructor normal-form-realisation
  field
    playerMap : Player E → Strategic.Player N
    profileMap : PlanProfile E → Strategic.Profile N
    outcomeMap : Outcome E → Strategic.Outcome N

    terminalOrContinuationOutcomeCommutes :
      (history : History E) →
      (plans : PlanProfile E) →
      outcomeMap (continuationOutcome E history plans)
      ≡ Strategic.outcome N (profileMap plans)

    realisationReference : String

open NormalFormRealisation public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data NormalFormNashMeansSequentialRationalityPermission : Set where

data SequentialRationalityMeansSubgamePerfectPermission : Set where

data SameTerminalOutcomeMeansSameHistoryPermission : Set where

data SameContinuationOutcomeMeansSameStrategyPermission : Set where

data ReachableHistoryMeansObservedHistoryPermission : Set where

data SubgamePerfectMeansHistoricalPredictionPermission : Set where

normalFormNashDoesNotAutomaticallyGiveSequentialRationality :
  NormalFormNashMeansSequentialRationalityPermission → ⊥
normalFormNashDoesNotAutomaticallyGiveSequentialRationality ()

sequentialRationalityDoesNotAutomaticallyGiveSubgamePerfection :
  SequentialRationalityMeansSubgamePerfectPermission → ⊥
sequentialRationalityDoesNotAutomaticallyGiveSubgamePerfection ()

sameTerminalOutcomeDoesNotRecoverHistory :
  SameTerminalOutcomeMeansSameHistoryPermission → ⊥
sameTerminalOutcomeDoesNotRecoverHistory ()

sameContinuationOutcomeDoesNotRecoverStrategy :
  SameContinuationOutcomeMeansSameStrategyPermission → ⊥
sameContinuationOutcomeDoesNotRecoverStrategy ()

reachabilityDoesNotByItselfProveObservedHistory :
  ReachableHistoryMeansObservedHistoryPermission → ⊥
reachabilityDoesNotByItselfProveObservedHistory ()

subgamePerfectionDoesNotPredictHistoricalPlay :
  SubgamePerfectMeansHistoricalPredictionPermission → ⊥
subgamePerfectionDoesNotPredictHistoricalPlay ()

record SequentialExtensiveFormBoundary : Set where
  constructor sequential-extensive-form-boundary
  field
    historiesExplicit : Bool
    continuationOutcomeExplicit : Bool
    localDeviationExplicit : Bool
    sequentialRationalityExplicit : Bool
    subgamePerfectionSeparate : Bool
    normalFormNashAutomaticallySequential : Bool
    sameOutcomeAutomaticallySameHistory : Bool

canonicalSequentialExtensiveFormBoundary : SequentialExtensiveFormBoundary
canonicalSequentialExtensiveFormBoundary =
  sequential-extensive-form-boundary
    true true true true true false false
