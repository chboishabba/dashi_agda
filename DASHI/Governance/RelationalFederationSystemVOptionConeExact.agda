module DASHI.Governance.RelationalFederationSystemVOptionConeExact where

-- DASHI-native structural cross-pollination. Beer/Cybersyn and
-- dashiTRADE prior owners retain their separate attribution.
-- A market trader is NOT a polity, and a score is NOT a mandate.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Trading.DashiTradeDreamOptionConeExact as Trade
import DASHI.Trading.TradingDeclaredRealizedViabilityBridgeExact as Realized
import DASHI.Finance.TradeRealizationSharpeAuthorityExact as Return
import DASHI.Governance.CyberneticClinicalInstitutionalRepairBridge as Cyber
import DASHI.Governance.FederatedSubsidiarityGovernanceExact as Base
import DASHI.Governance.RelationalFederationScopedViabilityExact as Scope

systemVSource : Cyber.GovernanceGateRow
systemVSource = Cyber.cybersynSystemFiveRow

systemVRemainsCandidate : Cyber.candidateOnly systemVSource ≡ true
systemVRemainsCandidate = refl

proposalDoesNotDetermineTradeAvailability :
  NF.FactorsThrough Trade.candidateObserver
    (λ s → Trade.actionAvailable s Trade.buyAction) → ⊥
proposalDoesNotDetermineTradeAvailability = Trade.noDirectionOnlyBuyClassifier

tradeEndpointCostNotIdentical : Return.lowRouteCost ≡ Return.churnRouteCost → ⊥
tradeEndpointCostNotIdentical = Return.lowAndChurnCostsDiffer

-- Separate feasible/admitted paths from an independently constituted
-- mandate and a scenario-relative evaluation. No scoring of authority.
-- No universal safe HOLD in a social/ecological system: even delay
-- or continuation can cause irreversible loss.
record CandidatePath {State ScopeID : Set}
  {ts : Base.TransitionSystem State}
  {e : Scope.ScopedExtension State ScopeID}
  (c : Scope.ScopedStepContract ts e)
  (source : State) : Set where
  field
    target : State
    admittedPath : Base.Reachable (Scope.admittedSystem c) source target

record Comparison {State ScopeID : Set}
  {ts : Base.TransitionSystem State}
  {e : Scope.ScopedExtension State ScopeID}
  {c : Scope.ScopedStepContract ts e} {s : State}
  (Scenario Coordinate : Set)
  (NoWorse : Scenario → Coordinate →
    CandidatePath c s → CandidatePath c s → Set)
  (StrictBetter : Scenario → Coordinate →
    CandidatePath c s → CandidatePath c s → Set)
  (candidate baseline : CandidatePath c s) : Set where
  field
    scenarioWitness : Scenario
    coordinateWitness : Coordinate
    noWorseEverywhere : (w : Scenario) (q : Coordinate) →
      NoWorse w q candidate baseline
    strictScenario : Scenario
    strictCoordinate : Coordinate
    strictSomewhere : StrictBetter strictScenario strictCoordinate candidate baseline

-- The same candidate and source must carry a mandate, independent review,
-- a justified comparison and baseline adequacy. These fields are external
-- evidence contracts; the record does not manufacture their inhabitants.
record GovernedSelection {State ScopeID : Set}
  {ts : Base.TransitionSystem State}
  {e : Scope.ScopedExtension State ScopeID}
  (c : Scope.ScopedStepContract ts e) (s : State)
  (Mandate Review BaselineAdequacy :
    CandidatePath c s → Set)
  (ComparisonEvidence :
    CandidatePath c s → CandidatePath c s → Set)
  (candidate baseline : CandidatePath c s) : Set where
  field
    sourceViable : Scope.JointViable e s
    mandate : Mandate candidate
    review : Review candidate
    baselineAdequate : BaselineAdequacy baseline
    comparison : ComparisonEvidence candidate baseline

selectedTargetViable :
  ∀ {State ScopeID : Set} {ts : Base.TransitionSystem State}
    {e : Scope.ScopedExtension State ScopeID}
    {c : Scope.ScopedStepContract ts e} {s : State}
    {M R B : CandidatePath c s → Set}
    {E : CandidatePath c s → CandidatePath c s → Set}
    {candidate baseline : CandidatePath c s} →
    GovernedSelection c s M R B E candidate baseline →
    Scope.JointViable e (CandidatePath.target candidate)
selectedTargetViable {c = c} {candidate = candidate} selected =
  Scope.reachableJointViability c (CandidatePath.admittedPath candidate)
    (GovernedSelection.sourceViable selected)

-- Actual execution and observed outcomes are distinct from the selection.
-- The returned observation is bound to the exact candidate and actual
-- target; actual target equality is not manufactured by the planner.
record Realization {State ScopeID : Set}
  {ts : Base.TransitionSystem State}
  {e : Scope.ScopedExtension State ScopeID}
  {c : Scope.ScopedStepContract ts e} {s : State}
  (candidate : CandidatePath c s)
  (Executed : CandidatePath c s → State → Set)
  (Observed : State → Set) : Set where
  field
    actualTarget : State
    executionWitness : Executed candidate actualTarget
    observationWitness : Observed actualTarget

-- Synthetic same-score / distinct mandate obstruction, not actual law.
data DecisionFixture : Set where
  authorised unapproved : DecisionFixture

forecastScore : DecisionFixture → Nat
forecastScore _ = 9

mandatePresent : DecisionFixture → Bool
mandatePresent authorised = true
mandatePresent unapproved = false

scoreCannotDetermineMandate :
  NF.FactorsThrough forecastScore mandatePresent → ⊥
scoreCannotDetermineMandate =
  NF.witnessRulesOutEveryFlatFactorisation
    (NF.nonFactorabilityWitness authorised unapproved refl (λ ()))

-- Specialization that consumes the actual comparison record rather than
-- an arbitrary boolean or scalar. Completeness of declared scenario and
-- coordinate domains is a separate evidence obligation.
RobustGovernedSelection :
  ∀ {State ScopeID : Set} {ts : Base.TransitionSystem State}
    {e : Scope.ScopedExtension State ScopeID}
    (c : Scope.ScopedStepContract ts e) (s : State)
    (Scenario Coordinate : Set)
    (M R B : CandidatePath c s → Set)
    (NoWorse StrictBetter : Scenario → Coordinate →
      CandidatePath c s → CandidatePath c s → Set) →
    CandidatePath c s → CandidatePath c s → Set
RobustGovernedSelection c s Scenario Coordinate M R B NoWorse StrictBetter =
  GovernedSelection c s M R B
    (Comparison Scenario Coordinate NoWorse StrictBetter)
