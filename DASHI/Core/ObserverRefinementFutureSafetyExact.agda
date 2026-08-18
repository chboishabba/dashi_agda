module DASHI.Core.ObserverRefinementFutureSafetyExact where

------------------------------------------------------------------------
-- STATIC OBSERVER REFINEMENT -> DYNAMIC FUTURE-LANGUAGE SAFETY
--
-- This welds the observer lattice introduced in the Brandt tranche to the
-- repository's pre-existing canonical FutureObservationLanguageQuotientExact.
--
-- Patrick Cousot and Radhia Cousot,
-- "Abstract interpretation: a unified lattice model for static analysis of
-- programs by construction or approximation of fixpoints", POPL 1977.
-- DOI: 10.1145/512950.512973.
--
-- David Blackwell,
-- "Equivalent Comparisons of Experiments", Annals of Mathematical Statistics
-- 24(2):265--272 (1953). DOI: 10.1214/aoms/1177729032.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.FutureObservationLanguageQuotientExact as Future
import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Core.TypedDependencyCore as Dependency

------------------------------------------------------------------------
-- If an observer already separates fine states, equality of its observation
-- identifies the starting states, so they have exactly the same future
-- observation language for every declared action/observation system.
------------------------------------------------------------------------

separatingObserverIsFutureLanguageSafe :
  ∀ {State Action Observation Coarse : Set}
    {system : Dependency.DependentActionSystem State Action}
    {project : State → Observation}
    {coarsen : Observer.Observer State Coarse} →
  Observer.Separating coarsen →
  Future.FutureLanguageSafeProjection system project coarsen
separatingObserverIsFutureLanguageSafe separating =
  Future.futureLanguageSafeProjection λ same →
    sameStateImpliesFutureEquivalent
      (separating _ _ same)
  where
    sameStateImpliesFutureEquivalent :
      ∀ {State Action Observation}
        {system : Dependency.DependentActionSystem State Action}
        {project : State → Observation}
        {left right : State} →
      left ≡ right →
      Future.FutureObservationEquivalent system project left right
    sameStateImpliesFutureEquivalent {left = left} refl =
      Future.futureEquivalentRefl left

------------------------------------------------------------------------
-- Safety is monotone upward in information: if a coarser observer is already
-- safe for a declared future language, every finer observer that refines it is
-- also safe for that SAME language.
--
-- The converse is intentionally absent.  The existing DynamicalQuotientSafety
-- module already shows that further coarsening may introduce future defects.
------------------------------------------------------------------------

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

record ObserverRefinementFutureSafetyBoundary : Set where
  constructor observerRefinementFutureSafetyBoundary
  field
    separatingObserverIsSafeForDeclaredFutureLanguage : Bool
    separatingObserverIsSafeForDeclaredFutureLanguageIsTrue :
      separatingObserverIsSafeForDeclaredFutureLanguage ≡ true
    safeCoarseImpliesSafeRefinement : Bool
    safeCoarseImpliesSafeRefinementIsTrue :
      safeCoarseImpliesSafeRefinement ≡ true
    safeFineImpliesArbitraryCoarseningSafe : Bool
    safeFineImpliesArbitraryCoarseningSafeIsFalse :
      safeFineImpliesArbitraryCoarseningSafe ≡ false
    futureSafetyMeansWorldIdentity : Bool
    futureSafetyMeansWorldIdentityIsFalse :
      futureSafetyMeansWorldIdentity ≡ false

canonicalObserverRefinementFutureSafetyBoundary :
  ObserverRefinementFutureSafetyBoundary
canonicalObserverRefinementFutureSafetyBoundary =
  observerRefinementFutureSafetyBoundary
    true refl
    true refl
    false refl
    false refl
