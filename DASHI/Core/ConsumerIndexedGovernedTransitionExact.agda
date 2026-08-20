module DASHI.Core.ConsumerIndexedGovernedTransitionExact where

------------------------------------------------------------------------
-- CONSUMER-INDEXED GOVERNED TRANSITIONS
--
-- This is the theorem-bearing core extracted from the SeaMeInIt / Animalexic /
-- LES cross-pollination.  A quotient is never called "safe" in the abstract:
-- safety is indexed by a declared consumer and action language, and authority
-- is preserved separately from observation.
--
-- Literature calibration:
--
-- Thomas Dean and Robert Givan,
-- "Model Minimization in Markov Decision Processes", AAAI 1997.
-- The paper supplies the classical state-partition / behavioural-minimisation
-- neighbourhood; the deterministic consumer-indexed construction below is a
-- DASHI theorem, not imported proof authority.
--
-- Patrick Cousot and Radhia Cousot,
-- "Abstract interpretation: a unified lattice model for static analysis of
-- programs by construction or approximation of fixpoints", POPL 1977.
-- DOI: 10.1145/512950.512973.
--
-- Sander Beckers and Joseph Y. Halpern,
-- "Abstracting Causal Models", AAAI 2019.
-- This motivates keeping action/intervention commutation distinct from mere
-- current-observation agreement.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong)

------------------------------------------------------------------------
-- Authority is deliberately ternary: abstention preserves the distinction
-- between an invalid candidate and an under-supported but potentially valid
-- candidate.
------------------------------------------------------------------------

data AuthorityDecision : Set where
  promote abstain reject : AuthorityDecision

------------------------------------------------------------------------
-- One transition system may expose different observations and action languages
-- to different consumers.
------------------------------------------------------------------------

record ConsumerIndexedGovernedTransition
    (State Action Consumer Observation : Set) : Set₁ where
  constructor consumerIndexedGovernedTransition
  field
    step : Action → State → State
    observe : Consumer → State → Observation
    declaredAction : Consumer → Action → Set
    authority : Consumer → State → AuthorityDecision

open ConsumerIndexedGovernedTransition public

------------------------------------------------------------------------
-- Finite-depth action/observation equivalence.
------------------------------------------------------------------------

FutureEquivalent :
  ∀ {State Action Consumer Observation} →
  ConsumerIndexedGovernedTransition State Action Consumer Observation →
  Consumer → Nat → State → State → Set
FutureEquivalent system consumer zero left right =
  observe system consumer left ≡ observe system consumer right
FutureEquivalent system consumer (suc depth) left right =
  (observe system consumer left ≡ observe system consumer right)
  × ((action : _) →
      declaredAction system consumer action →
      FutureEquivalent system consumer depth
        (step system action left)
        (step system action right))

futureEquivalentMonotone :
  ∀ {State Action Consumer Observation}
    {system : ConsumerIndexedGovernedTransition State Action Consumer Observation}
    {consumer : Consumer} {depth : Nat} {left right : State} →
  FutureEquivalent system consumer (suc depth) left right →
  FutureEquivalent system consumer depth left right
futureEquivalentMonotone {depth = zero} related = proj₁ related
futureEquivalentMonotone {depth = suc depth} related =
  proj₁ related , λ action allowed →
    futureEquivalentMonotone (proj₂ related action allowed)

------------------------------------------------------------------------
-- Declared traces and the standard finite-horizon consequence: agreement to
-- the trace length implies equal terminal observations.
------------------------------------------------------------------------

run :
  ∀ {State Action : Set} →
  (Action → State → State) → List Action → State → State
run stepFn [] state = state
run stepFn (action ∷ rest) state = run stepFn rest (stepFn action state)

data DeclaredTrace
    {State Action Consumer Observation : Set}
    (system : ConsumerIndexedGovernedTransition State Action Consumer Observation)
    (consumer : Consumer) : List Action → Set where
  traceNil : DeclaredTrace system consumer []
  traceCons :
    ∀ {action rest} →
    declaredAction system consumer action →
    DeclaredTrace system consumer rest →
    DeclaredTrace system consumer (action ∷ rest)

traceLength : ∀ {A : Set} → List A → Nat
traceLength [] = zero
traceLength (_ ∷ rest) = suc (traceLength rest)

traceObservationFromDepth :
  ∀ {State Action Consumer Observation}
    {system : ConsumerIndexedGovernedTransition State Action Consumer Observation}
    {consumer : Consumer}
    (actions : List Action)
    {left right : State} →
  DeclaredTrace system consumer actions →
  FutureEquivalent system consumer (traceLength actions) left right →
  observe system consumer (run (step system) actions left)
  ≡ observe system consumer (run (step system) actions right)
traceObservationFromDepth [] traceNil related = related
traceObservationFromDepth (action ∷ rest) (traceCons allowed declaredRest) related =
  traceObservationFromDepth rest declaredRest (proj₂ related action allowed)

------------------------------------------------------------------------
-- Consumer-safe abstraction: observation, dynamics AND authority descend.
------------------------------------------------------------------------

record ConsumerSafeAbstraction
    {Fine Coarse Action Consumer Observation : Set}
    (fine : ConsumerIndexedGovernedTransition Fine Action Consumer Observation)
    (project : Fine → Coarse) : Set₁ where
  constructor consumerSafeAbstraction
  field
    coarseStep : Action → Coarse → Coarse
    coarseObserve : Consumer → Coarse → Observation
    coarseAuthority : Consumer → Coarse → AuthorityDecision

    actionCommutes :
      ∀ action state →
      project (step fine action state)
      ≡ coarseStep action (project state)

    observationDescends :
      ∀ consumer state →
      observe fine consumer state
      ≡ coarseObserve consumer (project state)

    authorityDescends :
      ∀ consumer state →
      authority fine consumer state
      ≡ coarseAuthority consumer (project state)

open ConsumerSafeAbstraction public

sameProjectionSameObservation :
  ∀ {Fine Coarse Action Consumer Observation}
    {fine : ConsumerIndexedGovernedTransition Fine Action Consumer Observation}
    {project : Fine → Coarse}
    (abstraction : ConsumerSafeAbstraction fine project)
    (consumer : Consumer)
    {left right : Fine} →
  project left ≡ project right →
  observe fine consumer left ≡ observe fine consumer right
sameProjectionSameObservation abstraction consumer same
  rewrite observationDescends abstraction consumer left
        | observationDescends abstraction consumer right
        | same = refl

sameProjectionSameAuthority :
  ∀ {Fine Coarse Action Consumer Observation}
    {fine : ConsumerIndexedGovernedTransition Fine Action Consumer Observation}
    {project : Fine → Coarse}
    (abstraction : ConsumerSafeAbstraction fine project)
    (consumer : Consumer)
    {left right : Fine} →
  project left ≡ project right →
  authority fine consumer left ≡ authority fine consumer right
sameProjectionSameAuthority abstraction consumer same
  rewrite authorityDescends abstraction consumer left
        | authorityDescends abstraction consumer right
        | same = refl

stepPreservesProjectionEquality :
  ∀ {Fine Coarse Action Consumer Observation}
    {fine : ConsumerIndexedGovernedTransition Fine Action Consumer Observation}
    {project : Fine → Coarse}
    (abstraction : ConsumerSafeAbstraction fine project)
    (action : Action)
    {left right : Fine} →
  project left ≡ project right →
  project (step fine action left) ≡ project (step fine action right)
stepPreservesProjectionEquality abstraction action same
  rewrite actionCommutes abstraction action left
        | actionCommutes abstraction action right =
  cong (coarseStep abstraction action) same

------------------------------------------------------------------------
-- Main theorem: a consumer-safe abstraction induces bounded future equivalence
-- for every pair in one coarse fibre, for the declared consumer/action language.
------------------------------------------------------------------------

sameProjectionFutureEquivalent :
  ∀ {Fine Coarse Action Consumer Observation}
    {fine : ConsumerIndexedGovernedTransition Fine Action Consumer Observation}
    {project : Fine → Coarse}
    (abstraction : ConsumerSafeAbstraction fine project)
    (consumer : Consumer)
    (depth : Nat)
    {left right : Fine} →
  project left ≡ project right →
  FutureEquivalent fine consumer depth left right
sameProjectionFutureEquivalent abstraction consumer zero same =
  sameProjectionSameObservation abstraction consumer same
sameProjectionFutureEquivalent abstraction consumer (suc depth) same =
  sameProjectionSameObservation abstraction consumer same
  , λ action allowed →
      sameProjectionFutureEquivalent abstraction consumer depth
        (stepPreservesProjectionEquality abstraction action same)

------------------------------------------------------------------------
-- Important boundary: safety is indexed.  A quotient may be sound for one
-- consumer/action language and unsound for another; this module never promotes
-- consumer-local safety to world identity or to an undeclared consumer.
------------------------------------------------------------------------
