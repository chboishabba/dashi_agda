module DASHI.Governance.RelationalFederationScopedViabilityExact where

-- DASHI-native composition, not a political or empirical result.
-- Donors: ITIRPluralViabilityTSFVExact, FederatedSubsidiarityGovernanceExact,
-- KnowledgeProcessingSovereignCaptureExact, Brown/ESD scoped formation.
-- See Docs/SourceAttributionPolicy.md and relational federation roadmap.
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_; _×_)
import DASHI.Governance.FederatedSubsidiarityGovernanceExact as Base
import DASHI.Governance.ITIRPluralViabilityTSFVExact as Plural
import DASHI.Governance.KnowledgeProcessingSovereignCaptureExact as Access
import DASHI.Governance.RelationalFederationEducationFormationExact as Formation

-- State may itself be a time-indexed hyperfabric snapshot. All consumers
-- must refer to that SAME state and scope; independent existential witnesses
-- at unrelated times/places cannot fill this record.
record ScopedExtension (State Scope : Set) : Set₁ where
  field
    pluralEnvelope : Plural.PluralViabilityEnvelope State
    applies : State → Scope → Set
    situatedAuthority : State → Scope → Set
    futureOptions : State → Scope → Set
    independentAccess : State → Scope → Set
    formationAgency : State → Scope → Set
    ecologicalLearning : State → Scope → Set
    sourceReview : State → Scope → Set

open ScopedExtension

record ScopeWitness {State Scope : Set}
  (e : ScopedExtension State Scope) (s : State) (q : Scope) : Set where
  field
    authority : situatedAuthority e s q
    future : futureOptions e s q
    access : independentAccess e s q
    agency : formationAgency e s q
    learning : ecologicalLearning e s q
    review : sourceReview e s q

record JointViable {State Scope : Set}
  (e : ScopedExtension State Scope) (s : State) : Set where
  field
    plural : Plural.PluralViable (pluralEnvelope e) s
    everyAffectedScope : (q : Scope) → applies e s q → ScopeWitness e s q

-- Edge authority and evidence are indexed by the original edge, not merely
-- by a target label. Explicit per-edge closure is required, not assumed.
record ScopedStepContract {State Scope : Set}
  (ts : Base.TransitionSystem State) (e : ScopedExtension State Scope) : Set₁ where
  field
    pluralPreservation :
      Plural.PluralViabilityPreservingTransition ts (pluralEnvelope e)
    EdgeAdmission : Base.TransitionKind → State → State → Set
    scopePreservation :
      ∀ {k s t} → Base.step ts k s t → EdgeAdmission k s t →
      JointViable e s → (q : Scope) → applies e t q → ScopeWitness e t q

open ScopedStepContract

admittedSystem :
  ∀ {State Scope : Set} {ts : Base.TransitionSystem State}
    {e : ScopedExtension State Scope} →
  ScopedStepContract ts e → Base.TransitionSystem State
admittedSystem {ts = ts} c = record
  { step = λ k s t → Base.step ts k s t × EdgeAdmission c k s t }

preservesAdmittedStep :
  ∀ {State Scope : Set} {ts : Base.TransitionSystem State}
    {e : ScopedExtension State Scope} (c : ScopedStepContract ts e)
    {k s t} →
  Base.step (admittedSystem c) k s t → JointViable e s → JointViable e t
preservesAdmittedStep c (edge , admission) viable = record
  { plural = Plural.preservesPluralStep (pluralPreservation c) edge
      (JointViable.plural viable)
  ; everyAffectedScope = scopePreservation c edge admission viable }

reachableJointViability :
  ∀ {State Scope : Set} {ts : Base.TransitionSystem State}
    {e : ScopedExtension State Scope} (c : ScopedStepContract ts e)
    {s t} →
  Base.Reachable (admittedSystem c) s t → JointViable e s → JointViable e t
reachableJointViability c Base.reachableRefl viable = viable
reachableJointViability c (Base.reachableByStep edge) viable =
  preservesAdmittedStep c edge viable
reachableJointViability c (Base.reachableTrans left right) viable =
  reachableJointViability c right (reachableJointViability c left viable)

-- Reverse solve is a preimage in a relation, not an inverse function.
-- A common midpoint is a dependent witness; two independently named
-- endpoints cannot be glued without actual identity and paths.
ReverseCone :
  ∀ {State : Set} → Base.TransitionSystem State →
  (State → Set) → State → Set
ReverseCone {State} ts goal s =
  Σ State (λ t → Base.Reachable ts s t × goal t)

prependReachable :
  ∀ {State : Set} {ts : Base.TransitionSystem State}
    {goal : State → Set} {s m} →
  Base.Reachable ts s m → ReverseCone ts goal m → ReverseCone ts goal s
prependReachable left (t , right , proof) =
  t , Base.reachableTrans left right , proof

admittedMeet :
  ∀ {State Scope : Set} {ts : Base.TransitionSystem State}
    {e : ScopedExtension State Scope} (c : ScopedStepContract ts e)
    {goal : State → Set} {s m} →
  JointViable e s →
  Base.Reachable (admittedSystem c) s m →
  ReverseCone (admittedSystem c) goal m →
  ReverseCone (admittedSystem c) (λ t → JointViable e t × goal t) s
admittedMeet c viable left (t , right , proof) =
  t , Base.reachableTrans left right ,
  reachableJointViability c (Base.reachableTrans left right) viable , proof

-- Exact generic obstruction using the canonical access contract.
-- If one declared actor can block EVERY feasible route, the actor-relative
-- independence receipt cannot exist. No claim about actual providers.
commonGateObstructsIndependence :
  ∀ {User Capability Route Actor : Set}
    {system : Access.KnowledgeAccess User Capability Route Actor}
    {u : User} {cap : Capability} (a : Actor) →
  ((r : Route) → Access.Feasible system u cap r →
    Access.MayUnilaterallyBlock system a r) →
  Access.ActorIndependentKnowledge system u cap → ⊥
commonGateObstructsIndependence a cut independent =
  Access.routeOutsideActorControl independent a
    (cut (Access.routeForActor independent a)
      (Access.routeFeasible independent a))

-- Separate typed stock ledger for a single resource at a declared site/time.
-- The relation records an actual equality; no monetary proxy for physics.
record StockBalance (opening inflow consumption loss closing : Nat) : Set where
  constructor balance
  field
    conservation : opening + inflow ≡ consumption + (loss + closing)

-- Nonempty material witness must be provided independently for each
-- resource/site/interval; a generic contract creates no real quantities.
stockConstructive : (consumption loss closing : Nat) →
  StockBalance 0 (consumption + (loss + closing)) consumption loss closing
stockConstructive consumption loss closing = balance refl
