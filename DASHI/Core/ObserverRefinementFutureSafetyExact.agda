module DASHI.Core.ObserverRefinementFutureSafetyExact where

open import DASHI.Core.Prelude

import DASHI.Core.FutureObservationLanguageQuotientExact as Future
import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Core.TypedDependencyCore as Dependency

-- Blackwell, "Equivalent Comparisons of Experiments", 1953.
-- DOI: 10.1214/aoms/1177729032.
-- Cousot & Cousot, "Abstract interpretation...", POPL 1977.
-- DOI: 10.1145/512950.512973.

separatingObserverIsFutureLanguageSafe :
  ∀ {State Action Observation Coarse : Set}
    {system : Dependency.DependentActionSystem State Action}
    {project : State → Observation}
    {coarsen : Observer.Observer State Coarse} →
  Observer.Separating coarsen →
  Future.FutureLanguageSafeProjection system project coarsen
separatingObserverIsFutureLanguageSafe separating =
  Future.futureLanguageSafeProjection λ same →
    sameState (separating _ _ same)
  where
    sameState :
      ∀ {State Action Observation}
        {system : Dependency.DependentActionSystem State Action}
        {project : State → Observation}
        {x y : State} →
      x ≡ y → Future.FutureObservationEquivalent system project x y
    sameState {x = x} refl = Future.futureEquivalentRefl x

refinementPreservesFutureLanguageSafetyUpward :
  ∀ {State Action Observation Coarse Fine : Set}
    {system : Dependency.DependentActionSystem State Action}
    {project : State → Observation}
    {coarse : Observer.Observer State Coarse}
    {fine : Observer.Observer State Fine} →
  Observer.Refines coarse fine →
  Future.FutureLanguageSafeProjection system project coarse →
  Future.FutureLanguageSafeProjection system project fine
refinementPreservesFutureLanguageSafetyUpward refinement safe =
  Future.futureLanguageSafeProjection λ sameFine →
    Future.kernelContainedInFutureEquivalence safe
      (refinement _ _ sameFine)
