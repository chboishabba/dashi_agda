module DASHI.Cognition.PNF.CanonicalFutureObservableAlgebraExact where

------------------------------------------------------------------------
-- CANONICAL FUTURE OBSERVABLE ALGEBRA
--
-- A consumer-future-invariant observable on fine state is exactly an observable
-- on the canonical future quotient, pointwise.  This is the algebraic form of
-- the claim that the quotient is the complete carrier of all distinctions that
-- can matter to the declared future consumer.
--
-- No function extensionality or vector-space structure is assumed.  The result
-- is pointwise and therefore constructive in the current DASHI foundation.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.FutureObservationLanguageQuotientExact as Future
import DASHI.Core.StablePartitionCanonicalFutureBridgeExact as Bridge
import DASHI.Cognition.PNF.CanonicalFutureMinimalDynamicalRealizationExact as Minimal

record FutureInvariantObservable
    {State Action Observation : Set}
    {step : Action → State → State}
    {label : Action → String}
    {observe : State → Observation}
    (Value : Set) : Set₁ where
  constructor futureInvariantObservable
  field
    evaluate : State → Value
    respectsFutureEquivalence :
      ∀ {left right} →
      Future.FutureObservationEquivalent
        (Bridge.deterministicSystem step label) observe left right →
      evaluate left ≡ evaluate right

open FutureInvariantObservable public

------------------------------------------------------------------------
-- Descend a future-invariant observable to a sectioned canonical quotient.
------------------------------------------------------------------------

descendObservable :
  ∀ {State Action Observation Value}
    {step : Action → State → State}
    {label : Action → String}
    {observe : State → Observation}
    (presentation : Future.FutureEquivalencePresentation
      (Bridge.deterministicSystem step label) observe)
    (sectioned : Future.SectionedProjection (Future.classOf presentation)) →
  FutureInvariantObservable
    {step = step} {label = label} {observe = observe} Value →
  Future.QuotientCode presentation → Value
descendObservable presentation sectioned observable code =
  evaluate observable (Future.section sectioned code)

observableFactorsThroughCanonicalQuotient :
  ∀ {State Action Observation Value}
    {step : Action → State → State}
    {label : Action → String}
    {observe : State → Observation}
    (presentation : Future.FutureEquivalencePresentation
      (Bridge.deterministicSystem step label) observe)
    (sectioned : Future.SectionedProjection (Future.classOf presentation))
    (observable : FutureInvariantObservable
      {step = step} {label = label} {observe = observe} Value)
    (state : State) →
  evaluate observable state
  ≡ descendObservable presentation sectioned observable
      (Future.classOf presentation state)
observableFactorsThroughCanonicalQuotient
  presentation sectioned observable state =
  respectsFutureEquivalence observable
    (Future.classEqualitySound presentation
      (sym (Future.sectionRightInverse sectioned
        (Future.classOf presentation state))))

------------------------------------------------------------------------
-- Conversely, every quotient observable lifts to a future-invariant fine
-- observable because canonical future-equivalent states have equal class codes.
------------------------------------------------------------------------

liftQuotientObservable :
  ∀ {State Action Observation Value}
    {step : Action → State → State}
    {label : Action → String}
    {observe : State → Observation}
    (presentation : Future.FutureEquivalencePresentation
      (Bridge.deterministicSystem step label) observe) →
  (Future.QuotientCode presentation → Value) →
  FutureInvariantObservable
    {step = step} {label = label} {observe = observe} Value
liftQuotientObservable presentation quotientObservable =
  futureInvariantObservable
    (λ state → quotientObservable (Future.classOf presentation state))
    (λ equivalent →
      cong quotientObservable
        (Future.classEqualityComplete presentation equivalent))

------------------------------------------------------------------------
-- Pointwise round trips.  These replace function extensionality and state the
-- exact isomorphism needed by downstream operator theory.
------------------------------------------------------------------------

liftAfterDescendRecoversFineObservable :
  ∀ {State Action Observation Value}
    {step : Action → State → State}
    {label : Action → String}
    {observe : State → Observation}
    (presentation : Future.FutureEquivalencePresentation
      (Bridge.deterministicSystem step label) observe)
    (sectioned : Future.SectionedProjection (Future.classOf presentation))
    (observable : FutureInvariantObservable
      {step = step} {label = label} {observe = observe} Value)
    (state : State) →
  evaluate (liftQuotientObservable presentation
      (descendObservable presentation sectioned observable)) state
  ≡ evaluate observable state
liftAfterDescendRecoversFineObservable
  presentation sectioned observable state =
  sym (observableFactorsThroughCanonicalQuotient
    presentation sectioned observable state)

descendAfterLiftRecoversQuotientObservable :
  ∀ {State Action Observation Value}
    {step : Action → State → State}
    {label : Action → String}
    {observe : State → Observation}
    (presentation : Future.FutureEquivalencePresentation
      (Bridge.deterministicSystem step label) observe)
    (sectioned : Future.SectionedProjection (Future.classOf presentation))
    (quotientObservable : Future.QuotientCode presentation → Value)
    (code : Future.QuotientCode presentation) →
  descendObservable presentation sectioned
    (liftQuotientObservable presentation quotientObservable) code
  ≡ quotientObservable code
descendAfterLiftRecoversQuotientObservable
  presentation sectioned quotientObservable code =
  cong quotientObservable (Future.sectionRightInverse sectioned code)

------------------------------------------------------------------------
-- Koopman-like closure: pullback by a fine action preserves future-invariant
-- observables because future equivalence is an action congruence.
------------------------------------------------------------------------

actionPullback :
  ∀ {State Action Observation Value}
    {step : Action → State → State}
    {label : Action → String}
    {observe : State → Observation} →
  (action : Action) →
  FutureInvariantObservable
    {step = step} {label = label} {observe = observe} Value →
  FutureInvariantObservable
    {step = step} {label = label} {observe = observe} Value
actionPullback action observable =
  futureInvariantObservable
    (λ state → evaluate observable (step action state))
    (λ equivalent →
      respectsFutureEquivalence observable
        (Minimal.futureEquivalentStepCongruence equivalent action))

------------------------------------------------------------------------
-- The corresponding quotient pullback is ordinary precomposition with the
-- induced quotient action.  Fine and quotient pullbacks agree pointwise.
------------------------------------------------------------------------

quotientPullback :
  ∀ {State Action Observation Value}
    {step : Action → State → State}
    {label : Action → String}
    {observe : State → Observation}
    {presentation : Future.FutureEquivalencePresentation
      (Bridge.deterministicSystem step label) observe} →
  Minimal.CanonicalFutureDynamicalRealization
    step label observe presentation →
  Action →
  (Future.QuotientCode presentation → Value) →
  Future.QuotientCode presentation → Value
quotientPullback realization action observable code =
  observable (Minimal.quotientStep realization action code)

finePullbackFactorsThroughQuotientPullback :
  ∀ {State Action Observation Value}
    {step : Action → State → State}
    {label : Action → String}
    {observe : State → Observation}
    {presentation : Future.FutureEquivalencePresentation
      (Bridge.deterministicSystem step label) observe}
    (realization : Minimal.CanonicalFutureDynamicalRealization
      step label observe presentation)
    (action : Action)
    (quotientObservable : Future.QuotientCode presentation → Value)
    (state : State) →
  evaluate
    (actionPullback action
      (liftQuotientObservable presentation quotientObservable)) state
  ≡ quotientPullback realization action quotientObservable
      (Future.classOf presentation state)
finePullbackFactorsThroughQuotientPullback
  realization action quotientObservable state =
  cong quotientObservable (Minimal.actionDescends realization action state)

------------------------------------------------------------------------
-- Thus the complete future-invariant observable family is carried by the
-- canonical quotient, and action pullback closes on that family.  Linear spans,
-- spectra and Koopman matrices can now be added as coordinate choices on this
-- exact algebra rather than as substitutes for the semantic quotient.
------------------------------------------------------------------------
