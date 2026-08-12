module DASHI.Governance.EmancipatoryTransitionSafety where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Nat using (_≤_; _<_)

------------------------------------------------------------------------
-- Emancipatory transition safety.
--
-- This is a structural operator model, not a historical claim that any named
-- ideology or state satisfies it.  It separates state/public command from
-- private/material domination and requires a purported emancipatory transition
-- to state what happens to both.
--
-- Historical motivation (no DOI claimed here):
-- Karl Marx, Critique of the Gotha Programme (1875);
-- Karl Marx, The Civil War in France (1871);
-- Mikhail Bakunin, Statism and Anarchy (1873).
------------------------------------------------------------------------

record TransitionGeometry : Set₁ where
  field
    State : Set

    concentratedCommand : State → Nat
    materialDependency : State → Nat
    effectiveExit : State → Nat
    recoverableProvenance : State → Nat
    fascisticOperatorLoad : State → Nat
    publicDomination : State → Nat
    privateDomination : State → Nat

open TransitionGeometry public

record TransitionOperator (G : TransitionGeometry) : Set where
  constructor transitionOperator
  field
    step : State G → State G

open TransitionOperator public

------------------------------------------------------------------------
-- A safe transition changes reproduction geometry, not merely one coordinate.
------------------------------------------------------------------------

record SafeEmancipatoryTransition
    (G : TransitionGeometry)
    (T : TransitionOperator G) : Set₁ where
  field
    commandNonIncreasing :
      ∀ state →
      concentratedCommand G (step T state)
      ≤ concentratedCommand G state

    dependencyNonIncreasing :
      ∀ state →
      materialDependency G (step T state)
      ≤ materialDependency G state

    exitNonDecreasing :
      ∀ state →
      effectiveExit G state
      ≤ effectiveExit G (step T state)

    provenanceRecoverabilityNonDecreasing :
      ∀ state →
      recoverableProvenance G state
      ≤ recoverableProvenance G (step T state)

    fascisticLoadNonIncreasing :
      ∀ state →
      fascisticOperatorLoad G (step T state)
      ≤ fascisticOperatorLoad G state

open SafeEmancipatoryTransition public

------------------------------------------------------------------------
-- Self-obsolescence is local/conditional.  Requiring strict decrease at every
-- state would be impossible once necessity reaches zero.
------------------------------------------------------------------------

record InstitutionalNecessity
    (G : TransitionGeometry)
    (T : TransitionOperator G) : Set₁ where
  field
    necessity : State G → Nat

open InstitutionalNecessity public

record SelfObsoletingAt
    {G : TransitionGeometry}
    {T : TransitionOperator G}
    (N : InstitutionalNecessity G T)
    (state : State G) : Set where
  field
    necessityStrictlyFalls :
      necessity N (step T state) < necessity N state

open SelfObsoletingAt public

------------------------------------------------------------------------
-- Capture modes are independent: decreasing public command does not prove
-- decreasing total domination if private/material command grows.
------------------------------------------------------------------------

data CaptureMode : Set where
  stateCapture : CaptureMode
  capitalCapture : CaptureMode
  federationBureaucraticCapture : CaptureMode

record StateAbolitionWithoutDominationAbolition
    (G : TransitionGeometry)
    (T : TransitionOperator G) : Set₁ where
  field
    before : State G
    publicAfterIsZero : publicDomination G (step T before) ≡ 0
    PrivateDominationPersists : Set
    privatePersistence : PrivateDominationPersists

open StateAbolitionWithoutDominationAbolition public

------------------------------------------------------------------------
-- Relational domination: authority alone is not domination.  A witness needs
-- asymmetric constraint together with dependency and weak contest/exit.
------------------------------------------------------------------------

record PowerRelationSystem : Set₁ where
  field
    Actor : Set
    Domain : Set
    Constraint : Set
    ExitCost : Set

    constrains : Actor → Actor → Domain → Constraint → Set
    dependsOn : Actor → Actor → Domain → Set
    contestable : Actor → Actor → Domain → Set
    revocable : Actor → Actor → Domain → Set
    exitCost : Actor → Actor → Domain → ExitCost

open PowerRelationSystem public

record DominationWitness
    (P : PowerRelationSystem)
    (source target : Actor P)
    (domain : Domain P) : Set₁ where
  field
    constraint : Constraint P
    asymmetricConstraint : constrains P source target domain constraint
    dependency : dependsOn P target source domain
    ContestFailure : Set
    contestFailure : ContestFailure
    RevocationFailure : Set
    revocationFailure : RevocationFailure

open DominationWitness public

------------------------------------------------------------------------
-- Transition credibility: success should reduce dependence on structurally
-- privileged command rather than merely promise later abolition.
------------------------------------------------------------------------

record TransitionCredibility
    (G : TransitionGeometry)
    (T : TransitionOperator G) : Set₁ where
  field
    safe : SafeEmancipatoryTransition G T
    NecessityModel : InstitutionalNecessity G T
    selfObsoletingWhereRequired :
      (state : State G) → Set

open TransitionCredibility public

------------------------------------------------------------------------
-- No theorem equates decentralisation with antifascism.
------------------------------------------------------------------------

data DecentralisationAutomaticallyAntifascist : Set where

decentralisationDoesNotAutomaticallyCertifyAntifascism :
  DecentralisationAutomaticallyAntifascist → ⊥
decentralisationDoesNotAutomaticallyCertifyAntifascism ()
