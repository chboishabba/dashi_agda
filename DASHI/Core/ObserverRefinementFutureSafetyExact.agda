module DASHI.Core.ObserverRefinementFutureSafetyExact where

open import DASHI.Core.Prelude

import DASHI.Core.FutureObservationLanguageQuotientExact as Future
import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Core.TypedDependencyCore as Dependency

-- David Blackwell, "Equivalent Comparisons of Experiments", 1953.
-- DOI: 10.1214/aoms/1177729032.
-- Patrick Cousot and Radhia Cousot,
-- "Abstract interpretation: a unified lattice model for static analysis of
-- programs by construction or approximation of fixpoints", POPL 1977.
-- DOI: 10.1145/512950.512973.

------------------------------------------------------------------------
-- Separating observation is a sufficient, deliberately strong route to
-- future-language safety.
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
    sameState (separating _ _ same)
  where
    sameState :
      ∀ {State Action Observation}
        {system : Dependency.DependentActionSystem State Action}
        {project : State → Observation}
        {x y : State} →
      x ≡ y → Future.FutureObservationEquivalent system project x y
    sameState {x = x} refl = Future.futureEquivalentRefl x

------------------------------------------------------------------------
-- Future-language safety is monotone upward in retained information.
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

------------------------------------------------------------------------
-- Universal-property weld.
--
-- Once a refinement has become future-language safe, any SECTIONED
-- presentation of that refined observer must still factor the canonical
-- future-equivalence code.  Thus a refinement is allowed to retain extra
-- provenance/audit distinctions without promoting them to dynamically
-- necessary distinctions.
------------------------------------------------------------------------

safeRefinementFactorsThroughCanonicalFutureQuotient :
  ∀ {State Action Observation Coarse Fine}
    {system : Dependency.DependentActionSystem State Action}
    {project : State → Observation}
    {coarse : Observer.Observer State Coarse}
    {fine : Observer.Observer State Fine} →
  (presentation : Future.FutureEquivalencePresentation system project) →
  Observer.Refines coarse fine →
  Future.FutureLanguageSafeProjection system project coarse →
  Future.SectionedProjection fine →
  Future.FactorizationThroughFutureQuotient presentation
safeRefinementFactorsThroughCanonicalFutureQuotient
  presentation refinement safe sectioned =
  Future.sectionedSafeProjectionFactors
    presentation
    (refinementPreservesFutureLanguageSafetyUpward refinement safe)
    sectioned

separatingSectionedObserverFactorsCanonicalFutureQuotient :
  ∀ {State Action Observation Fine}
    {system : Dependency.DependentActionSystem State Action}
    {project : State → Observation}
    {fine : Observer.Observer State Fine} →
  (presentation : Future.FutureEquivalencePresentation system project) →
  Observer.Separating fine →
  Future.SectionedProjection fine →
  Future.FactorizationThroughFutureQuotient presentation
separatingSectionedObserverFactorsCanonicalFutureQuotient
  presentation separating sectioned =
  Future.sectionedSafeProjectionFactors
    presentation
    (separatingObserverIsFutureLanguageSafe separating)
    sectioned

record ObserverRefinementFutureSafetyBoundary : Set where
  constructor observerRefinementFutureSafetyBoundary
  field
    separatingObserverIsSafeForDeclaredFutureLanguage : Bool
    separatingObserverIsSafeForDeclaredFutureLanguageIsTrue :
      separatingObserverIsSafeForDeclaredFutureLanguage ≡ true
    safeCoarseImpliesSafeRefinement : Bool
    safeCoarseImpliesSafeRefinementIsTrue :
      safeCoarseImpliesSafeRefinement ≡ true
    safeRefinementMayRetainMoreThanCanonicalFutureCode : Bool
    safeRefinementMayRetainMoreThanCanonicalFutureCodeIsTrue :
      safeRefinementMayRetainMoreThanCanonicalFutureCode ≡ true
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
    true refl true refl true refl false refl false refl
