module DASHI.GameTheory.CooperativeCoalitionBargainingCoreExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- COOPERATIVE / COALITIONAL GAME CORE
--
-- Coalitional blocking is a different stability notion from unilateral Nash
-- deviation.  The cooperative core is represented directly as grand-coalition
-- feasibility plus absence of a blocking coalition.  Bargaining is separate
-- again: a feasible outcome, disagreement point and player-relative preference
-- relation do not manufacture any particular bargaining solution theorem.
------------------------------------------------------------------------

record CooperativeGame : Set₁ where
  constructor cooperative-game
  field
    Player Coalition Allocation Value : Set

    grandCoalition : Coalition
    Member : Player → Coalition → Set

    coalitionValue : Coalition → Value

    FeasibleFor : Allocation → Coalition → Set

    BlockingAlternative :
      Coalition →
      Allocation →
      Allocation → Set

    blockAlternativeFeasible :
      (coalition : Coalition) →
      (statusQuo alternative : Allocation) →
      BlockingAlternative coalition statusQuo alternative →
      FeasibleFor alternative coalition

    gameReference : String
    coalitionReference : String
    feasibilityReference : String

open CooperativeGame public

CoalitionBlocks :
  (G : CooperativeGame) →
  Coalition G →
  Allocation G → Set
CoalitionBlocks G coalition statusQuo =
  Σ (Allocation G)
    (λ alternative →
      BlockingAlternative G coalition statusQuo alternative)

record CoreAllocation (G : CooperativeGame) : Set₁ where
  constructor core-allocation
  field
    allocation : Allocation G

    grandCoalitionFeasible :
      FeasibleFor G allocation (grandCoalition G)

    noBlockingCoalition :
      (coalition : Coalition G) →
      CoalitionBlocks G coalition allocation →
      ⊥

    coreReference : String

open CoreAllocation public

coreBlocksEveryReceiptedCoalitionalDeviation :
  ∀ {G : CooperativeGame} →
  (C : CoreAllocation G) →
  (coalition : Coalition G) →
  CoalitionBlocks G coalition (allocation C) →
  ⊥
coreBlocksEveryReceiptedCoalitionalDeviation C coalition =
  noBlockingCoalition C coalition

------------------------------------------------------------------------
-- Bargaining surface.
------------------------------------------------------------------------

record BargainingProblem : Set₁ where
  constructor bargaining-problem
  field
    Player Outcome : Set

    Feasible : Outcome → Set
    disagreement : Outcome

    WeaklyPrefers : Player → Outcome → Outcome → Set
    StrictlyPrefers : Player → Outcome → Outcome → Set

    strictImpliesWeak :
      (player : Player) →
      (better worse : Outcome) →
      StrictlyPrefers player better worse →
      WeaklyPrefers player better worse

    problemReference : String
    disagreementReference : String
    preferenceReference : String

open BargainingProblem public

ParetoWeaklyImprovesOutcome :
  (B : BargainingProblem) →
  Outcome B →
  Outcome B → Set
ParetoWeaklyImprovesOutcome B before after =
  (player : Player B) →
  WeaklyPrefers B player after before

record BargainingSolution
    (B : BargainingProblem) : Set₁ where
  constructor bargaining-solution
  field
    solution : Outcome B
    feasible : Feasible B solution

    individuallyRational :
      (player : Player B) →
      WeaklyPrefers B player solution (disagreement B)

    ParetoEfficient : Set
    paretoEfficient : ParetoEfficient

    solutionReference : String

open BargainingSolution public

------------------------------------------------------------------------
-- Optional bridge: bargaining solution as a cooperative allocation.
------------------------------------------------------------------------

record BargainingCooperativeRealisation
    (B : BargainingProblem)
    (G : CooperativeGame) : Set₁ where
  constructor bargaining-cooperative-realisation
  field
    outcomeToAllocation : Outcome B → Allocation G

    feasibleGrandCoalitionCommutes :
      (outcome : Outcome B) →
      Feasible B outcome →
      FeasibleFor G
        (outcomeToAllocation outcome)
        (grandCoalition G)

    realisationReference : String

open BargainingCooperativeRealisation public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data NashMeansCorePermission : Set where

data CoreMeansNashPermission : Set where

data CoreAllocationMeansUniquePermission : Set where

data FeasibleMeansFairPermission : Set where

data ParetoMeansFairPermission : Set where

data IndividualRationalityMeansTruthPermission : Set where

data BargainingProblemMeansNashBargainingSolutionPermission : Set where

data CoalitionValueMeansMoralWorthPermission : Set where

nashDoesNotAutomaticallyGiveCooperativeCore : NashMeansCorePermission → ⊥
nashDoesNotAutomaticallyGiveCooperativeCore ()

cooperativeCoreDoesNotAutomaticallyGiveNash : CoreMeansNashPermission → ⊥
cooperativeCoreDoesNotAutomaticallyGiveNash ()

coreNeedNotBeUnique : CoreAllocationMeansUniquePermission → ⊥
coreNeedNotBeUnique ()

feasibilityDoesNotCreateFairness : FeasibleMeansFairPermission → ⊥
feasibilityDoesNotCreateFairness ()

paretoEfficiencyDoesNotCreateFairness : ParetoMeansFairPermission → ⊥
paretoEfficiencyDoesNotCreateFairness ()

individualRationalityDoesNotCreateTruthAuthority :
  IndividualRationalityMeansTruthPermission → ⊥
individualRationalityDoesNotCreateTruthAuthority ()

bargainingCarrierDoesNotManufactureNashBargainingTheorem :
  BargainingProblemMeansNashBargainingSolutionPermission → ⊥
bargainingCarrierDoesNotManufactureNashBargainingTheorem ()

coalitionValueDoesNotCreateMoralWorth : CoalitionValueMeansMoralWorthPermission → ⊥
coalitionValueDoesNotCreateMoralWorth ()

record CooperativeBargainingBoundary : Set where
  constructor cooperative-bargaining-boundary
  field
    coalitionBlockingExplicit : Bool
    coreSeparateFromNash : Bool
    bargainingDisagreementExplicit : Bool
    bargainingPreferencePlayerRelative : Bool
    paretoSeparateFromFairness : Bool
    nashBargainingTheoremInventedHere : Bool

canonicalCooperativeBargainingBoundary : CooperativeBargainingBoundary
canonicalCooperativeBargainingBoundary =
  cooperative-bargaining-boundary true true true true true false
