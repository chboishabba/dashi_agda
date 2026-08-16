module DASHI.Core.StablePartitionCanonicalFutureBridgeExact where

------------------------------------------------------------------------
-- INTERNAL PRODUCER RECONCILIATION
--
-- Ported without changing theorem content from the live PR #548 future-safe
-- compression lane.  It proves that a stable finite-depth deterministic
-- observation refinement is exactly canonical future observational
-- equivalence for the declared action/observation language.
--
-- This is a DASHI theorem family; no external source is claimed as proof
-- authority for the exact construction.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AdmissibleReachability as Reachability
import DASHI.Core.FutureObservationLanguageQuotientExact as Future
import DASHI.Core.GenericFuturePartitionRefinementExact as Refinement
import DASHI.Core.TypedDependencyCore as Dependency

record ExactPost
    {State Action : Set}
    (step : Action → State → State)
    (before : State)
    (action : Action)
    (after : State) : Set where
  constructor exactPost
  field
    afterIsStep : after ≡ step action before

open ExactPost public

deterministicSystem :
  ∀ {State Action : Set} →
  (step : Action → State → State) →
  (actionLabel : Action → String) →
  Dependency.DependentActionSystem State Action
deterministicSystem step label = record
  { Precondition = λ state action → ⊤
  ; Postcondition = ExactPost step
  ; actionLabel = label
  }

canonicalAction :
  ∀ {State Action}
    {step : Action → State → State}
    {label : Action → String}
    (state : State) (action : Action) →
  Dependency.AdmissibleAction
    (deterministicSystem step label) state action
canonicalAction state action = record
  { precondition = tt
  ; after = step action state
  ; postcondition = exactPost refl
  ; dependencyReceipt = "canonical deterministic action"
  }

canonicalExecutes :
  ∀ {State Action}
    {step : Action → State → State}
    {label : Action → String}
    (actions : List Action) (state : State) →
  Reachability.Executes
    (deterministicSystem step label)
    actions state (Refinement.run step actions state)
canonicalExecutes [] state = Reachability.executesNil
canonicalExecutes (action ∷ rest) state =
  Reachability.executesCons
    (canonicalAction state action)
    (canonicalExecutes rest (step action state))

executionTargetIsRun :
  ∀ {State Action}
    {step : Action → State → State}
    {label : Action → String}
    {actions : List Action}
    {before after : State} →
  Reachability.Executes
    (deterministicSystem step label) actions before after →
  after ≡ Refinement.run step actions before
executionTargetIsRun Reachability.executesNil = refl
executionTargetIsRun
  (Reachability.executesCons admissible rest)
  with afterIsStep (Dependency.postcondition admissible)
... | refl = executionTargetIsRun rest

TraceEquivalent :
  ∀ {State Action Observation : Set} →
  (State → Observation) →
  (Action → State → State) →
  State → State → Set
TraceEquivalent {Action = Action} observe step left right =
  (actions : List Action) →
  observe (Refinement.run step actions left)
  ≡ observe (Refinement.run step actions right)

traceEquivalentImpliesCanonicalFutureEquivalent :
  ∀ {State Action Observation}
    {observe : State → Observation}
    {step : Action → State → State}
    {label : Action → String}
    {left right : State} →
  TraceEquivalent observe step left right →
  Future.FutureObservationEquivalent
    (deterministicSystem step label) observe left right
traceEquivalentImpliesCanonicalFutureEquivalent
  {Action = Action} {Observation = Observation}
  {observe = observe} {step = step} {label = label}
  {left = left} {right = right}
  traceEqual =
  Future.futureObservationEquivalent λ actions observation →
    Future.logicalIff (forwardWitness actions observation) (backwardWitness actions observation)
  where
    forwardWitness :
      (actions : List Action) → (observation : Observation) →
      Future.FutureObservation
        (deterministicSystem step label) observe left actions observation →
      Future.FutureObservation
        (deterministicSystem step label) observe right actions observation
    forwardWitness actions observation
      (Future.futureObservation after execution observed)
      with executionTargetIsRun execution
    ... | refl =
      Future.futureObservation
        (Refinement.run step actions right)
        (canonicalExecutes actions right)
        (trans (sym (traceEqual actions)) observed)

    backwardWitness :
      (actions : List Action) → (observation : Observation) →
      Future.FutureObservation
        (deterministicSystem step label) observe right actions observation →
      Future.FutureObservation
        (deterministicSystem step label) observe left actions observation
    backwardWitness actions observation
      (Future.futureObservation after execution observed)
      with executionTargetIsRun execution
    ... | refl =
      Future.futureObservation
        (Refinement.run step actions left)
        (canonicalExecutes actions left)
        (trans (traceEqual actions) observed)

canonicalFutureEquivalentImpliesTraceEquivalent :
  ∀ {State Action Observation}
    {observe : State → Observation}
    {step : Action → State → State}
    {label : Action → String}
    {left right : State} →
  Future.FutureObservationEquivalent
    (deterministicSystem step label) observe left right →
  TraceEquivalent observe step left right
canonicalFutureEquivalentImpliesTraceEquivalent
  {Observation = Observation}
  {observe = observe} {step = step} {label = label}
  {left = left} {right = right}
  equivalent actions =
  sym rightObservedAsLeft
  where
    leftObservation : Observation
    leftObservation = observe (Refinement.run step actions left)

    leftWitness :
      Future.FutureObservation
        (deterministicSystem step label) observe left actions leftObservation
    leftWitness =
      Future.futureObservation
        (Refinement.run step actions left)
        (canonicalExecutes actions left)
        refl

    rightWitness :
      Future.FutureObservation
        (deterministicSystem step label) observe right actions leftObservation
    rightWitness =
      Future.forward
        (Future.sameFutureLanguage equivalent actions leftObservation)
        leftWitness

    rightObservedAsLeft :
      observe (Refinement.run step actions right) ≡ leftObservation
    rightObservedAsLeft with rightWitness
    ... | Future.futureObservation after execution observed
      with executionTargetIsRun execution
    ... | refl = observed

traceEquivalentImpliesEveryDepth :
  ∀ {State Action Observation}
    {observe : State → Observation}
    {step : Action → State → State}
    {left right : State} →
  TraceEquivalent observe step left right →
  (depth : Nat) →
  Refinement.RefinesToDepth depth observe step left right
traceEquivalentImpliesEveryDepth traceEqual zero = traceEqual []
traceEquivalentImpliesEveryDepth traceEqual (suc depth) =
  traceEqual [] , λ action →
    traceEquivalentImpliesEveryDepth
      (λ rest → traceEqual (action ∷ rest))
      depth

dropLeadingDepth :
  ∀ {State Action Observation}
    {observe : State → Observation}
    {step : Action → State → State}
    {left right : State}
    (drop keep : Nat) →
  Refinement.RefinesToDepth (drop + keep) observe step left right →
  Refinement.RefinesToDepth keep observe step left right
dropLeadingDepth zero keep related = related
dropLeadingDepth (suc drop) keep related =
  dropLeadingDepth drop keep (Refinement.refinementMonotone related)

stableRefinementImpliesTraceEquivalent :
  ∀ {State Action Observation depth}
    {observe : State → Observation}
    {step : Action → State → State}
    (stable : Refinement.StableAt depth observe step)
    {left right : State} →
  Refinement.RefinesToDepth depth observe step left right →
  TraceEquivalent observe step left right
stableRefinementImpliesTraceEquivalent
  {depth = depth} stable related actions =
  Refinement.traceObservationFromDepth actions
    (dropLeadingDepth depth (length actions)
      (Refinement.stablePairLifts stable related (length actions)))

stableRefinementExactlyCanonicalFuture :
  ∀ {State Action Observation depth}
    {observe : State → Observation}
    {step : Action → State → State}
    {label : Action → String}
    (stable : Refinement.StableAt depth observe step)
    (left right : State) →
  (Refinement.RefinesToDepth depth observe step left right →
    Future.FutureObservationEquivalent
      (deterministicSystem step label) observe left right)
  ×
  (Future.FutureObservationEquivalent
      (deterministicSystem step label) observe left right →
    Refinement.RefinesToDepth depth observe step left right)
stableRefinementExactlyCanonicalFuture {depth = depth} stable left right =
  (λ related →
    traceEquivalentImpliesCanonicalFutureEquivalent
      (stableRefinementImpliesTraceEquivalent stable related))
  ,
  (λ equivalent →
    traceEquivalentImpliesEveryDepth
      (canonicalFutureEquivalentImpliesTraceEquivalent equivalent)
      depth)
