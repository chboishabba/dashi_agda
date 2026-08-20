module DASHI.Core.ConsumerIndexedGovernedTransitionExact where

------------------------------------------------------------------------
-- CONSUMER-INDEXED GOVERNED TRANSITIONS
--
-- A quotient is never called safe in the abstract: safety is indexed by a
-- declared consumer and action language, and authority is preserved separately
-- from observation.
--
-- Thomas Dean and Robert Givan, "Model Minimization in Markov Decision
-- Processes", AAAI 1997.
-- Patrick Cousot and Radhia Cousot, "Abstract interpretation: a unified lattice
-- model for static analysis of programs by construction or approximation of
-- fixpoints", POPL 1977. DOI: 10.1145/512950.512973.
-- Sander Beckers and Joseph Y. Halpern, "Abstracting Causal Models", AAAI 2019.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong)

data AuthorityDecision : Set where
  promote abstain reject : AuthorityDecision

record ConsumerIndexedGovernedTransition
    (State Action Consumer Observation : Set) : Set₁ where
  constructor consumerIndexedGovernedTransition
  field
    step : Action → State → State
    observe : Consumer → State → Observation
    declaredAction : Consumer → Action → Set
    authority : Consumer → State → AuthorityDecision

open ConsumerIndexedGovernedTransition public

FutureEquivalent :
  ∀ {State Action Consumer Observation} →
  ConsumerIndexedGovernedTransition State Action Consumer Observation →
  Consumer → Nat → State → State → Set
FutureEquivalent system consumer zero left right =
  observe system consumer left ≡ observe system consumer right
FutureEquivalent {Action = Action} system consumer (suc depth) left right =
  (observe system consumer left ≡ observe system consumer right)
  × ((action : Action) →
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
      project (step fine action state) ≡ coarseStep action (project state)
    observationDescends :
      ∀ consumer state →
      observe fine consumer state ≡ coarseObserve consumer (project state)
    authorityDescends :
      ∀ consumer state →
      authority fine consumer state ≡ coarseAuthority consumer (project state)

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
sameProjectionSameObservation abstraction consumer {left} {right} same
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
sameProjectionSameAuthority abstraction consumer {left} {right} same
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
stepPreservesProjectionEquality abstraction action {left} {right} same
  rewrite actionCommutes abstraction action left
        | actionCommutes abstraction action right =
  cong (coarseStep abstraction action) same

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
