module DASHI.Core.ObserverFactorizedRefinementExact where

open import DASHI.Core.Prelude

import DASHI.Core.FutureObservationLanguageQuotientExact as Future
import DASHI.Core.ObserverRefinementFutureSafetyExact as FutureSafety
import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Core.TypedDependencyCore as Dependency

record FactorizedRefinement
    {State Coarse Fine : Set}
    (coarse : Observer.Observer State Coarse)
    (fine : Observer.Observer State Fine) : Set₁ where
  constructor factorizedRefinement
  field
    factor : Fine → Coarse
    factorizes : (x : State) → coarse x ≡ factor (fine x)

open FactorizedRefinement public

identityFactorizedRefinement :
  ∀ {State Value : Set}
    (observe : Observer.Observer State Value) →
  FactorizedRefinement observe observe
identityFactorizedRefinement observe =
  factorizedRefinement (λ x → x) (λ x → refl)

factorizedRefinementImpliesRefines :
  ∀ {State Coarse Fine : Set}
    {coarse : Observer.Observer State Coarse}
    {fine : Observer.Observer State Fine} →
  FactorizedRefinement coarse fine →
  Observer.Refines coarse fine
factorizedRefinementImpliesRefines refinement x y sameFine =
  trans
    (factorizes refinement x)
    (trans
      (cong (factor refinement) sameFine)
      (sym (factorizes refinement y)))

composeFactorizedRefinement :
  ∀ {State Coarse Middle Fine : Set}
    {coarse : Observer.Observer State Coarse}
    {middle : Observer.Observer State Middle}
    {fine : Observer.Observer State Fine} →
  FactorizedRefinement coarse middle →
  FactorizedRefinement middle fine →
  FactorizedRefinement coarse fine
composeFactorizedRefinement first second =
  factorizedRefinement
    (λ fineValue → factor first (factor second fineValue))
    (λ x →
      trans
        (factorizes first x)
        (cong (factor first) (factorizes second x)))

pairObserverFactorsToLeft :
  ∀ {State A B : Set}
    (left : Observer.Observer State A)
    (right : Observer.Observer State B) →
  FactorizedRefinement left (Observer.pairObserver left right)
pairObserverFactorsToLeft left right =
  factorizedRefinement proj₁ (λ x → refl)

pairObserverFactorsToRight :
  ∀ {State A B : Set}
    (left : Observer.Observer State A)
    (right : Observer.Observer State B) →
  FactorizedRefinement right (Observer.pairObserver left right)
pairObserverFactorsToRight left right =
  factorizedRefinement proj₂ (λ x → refl)

factorizedRefinementPreservesFutureLanguageSafety :
  ∀ {State Action Observation Coarse Fine : Set}
    {system : Dependency.DependentActionSystem State Action}
    {project : State → Observation}
    {coarse : Observer.Observer State Coarse}
    {fine : Observer.Observer State Fine} →
  FactorizedRefinement coarse fine →
  Future.FutureLanguageSafeProjection system project coarse →
  Future.FutureLanguageSafeProjection system project fine
factorizedRefinementPreservesFutureLanguageSafety refinement =
  FutureSafety.refinementPreservesFutureLanguageSafetyUpward
    (factorizedRefinementImpliesRefines refinement)

record ObserverFactorizedRefinementBoundary : Set where
  constructor observerFactorizedRefinementBoundary
  field
    factorizationImpliesKernelRefinement : Bool
    factorizationImpliesKernelRefinementIsTrue :
      factorizationImpliesKernelRefinement ≡ true
    factorizedRefinementsCompose : Bool
    factorizedRefinementsComposeIsTrue : factorizedRefinementsCompose ≡ true
    factorizationAloneMeansFineObserverSeparating : Bool
    factorizationAloneMeansFineObserverSeparatingIsFalse :
      factorizationAloneMeansFineObserverSeparating ≡ false

canonicalObserverFactorizedRefinementBoundary :
  ObserverFactorizedRefinementBoundary
canonicalObserverFactorizedRefinementBoundary =
  observerFactorizedRefinementBoundary true refl true refl false refl
