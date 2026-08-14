module DASHI.Cognition.PNF.CanonicalFutureMinimalDynamicalRealizationExact where

------------------------------------------------------------------------
-- CANONICAL FUTURE QUOTIENT -> MINIMAL DYNAMICAL REALIZATION
--
-- The canonical future quotient already answers which fine states may coincide.
-- Deterministic actions descend to those classes.  With a section, this yields
-- a concrete quotient action, while every other sectioned future-safe
-- representation factors onto the canonical quotient.  This is minimality in
-- the exact information/quotient order, not yet minimum vector-space dimension.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.FutureObservationLanguageQuotientExact as Future
import DASHI.Core.GenericFuturePartitionRefinementExact as Refinement
import DASHI.Core.StablePartitionCanonicalFutureBridgeExact as Bridge
import DASHI.Cognition.PNF.FutureSufficientInvariantSubspaceExact as Invariant

futureEquivalentStepCongruence :
  ∀ {State Action Observation}
    {step : Action → State → State}
    {label : Action → String}
    {observe : State → Observation}
    {left right : State} →
  Future.FutureObservationEquivalent
    (Bridge.deterministicSystem step label) observe left right →
  (action : Action) →
  Future.FutureObservationEquivalent
    (Bridge.deterministicSystem step label) observe
    (step action left) (step action right)
futureEquivalentStepCongruence equivalent action =
  Bridge.traceEquivalentImpliesCanonicalFutureEquivalent
    (λ actions →
      Bridge.canonicalFutureEquivalentImpliesTraceEquivalent equivalent
        (action ∷ actions))

record CanonicalFutureDynamicalRealization
    {State Action Observation : Set}
    (step : Action → State → State)
    (label : Action → String)
    (observe : State → Observation)
    (presentation : Future.FutureEquivalencePresentation
      (Bridge.deterministicSystem step label) observe) : Set₁ where
  constructor canonicalFutureDynamicalRealization
  field
    quotientSectioned : Future.SectionedProjection (Future.classOf presentation)
    quotientStep :
      Action → Future.QuotientCode presentation → Future.QuotientCode presentation
    actionDescends :
      (action : Action) (state : State) →
      Future.classOf presentation (step action state)
      ≡ quotientStep action (Future.classOf presentation state)

open CanonicalFutureDynamicalRealization public

compileCanonicalQuotientDynamics :
  ∀ {State Action Observation}
    {step : Action → State → State}
    {label : Action → String}
    {observe : State → Observation}
    (presentation : Future.FutureEquivalencePresentation
      (Bridge.deterministicSystem step label) observe) →
  (sectioned : Future.SectionedProjection (Future.classOf presentation)) →
  CanonicalFutureDynamicalRealization step label observe presentation
compileCanonicalQuotientDynamics
  {step = step} {label = label} {observe = observe}
  presentation sectioned =
  canonicalFutureDynamicalRealization sectioned quotientStep proof
  where
    quotientStep :
      Action → Future.QuotientCode presentation → Future.QuotientCode presentation
    quotientStep action code =
      Future.classOf presentation
        (step action (Future.section sectioned code))

    proof : (action : Action) (state : State) →
      Future.classOf presentation (step action state)
      ≡ quotientStep action (Future.classOf presentation state)
    proof action state =
      Future.classEqualityComplete presentation
        (futureEquivalentStepCongruence
          (Future.classEqualitySound presentation
            (sym (Future.sectionRightInverse sectioned
              (Future.classOf presentation state))))
          action)

runQuotient :
  ∀ {State Action Observation}
    {step : Action → State → State}
    {label : Action → String}
    {observe : State → Observation}
    {presentation : Future.FutureEquivalencePresentation
      (Bridge.deterministicSystem step label) observe} →
  CanonicalFutureDynamicalRealization step label observe presentation →
  List Action → Future.QuotientCode presentation → Future.QuotientCode presentation
runQuotient realization [] code = code
runQuotient realization (action ∷ actions) code =
  runQuotient realization actions (quotientStep realization action code)

canonicalEncodingCommutesWithTrace :
  ∀ {State Action Observation}
    {step : Action → State → State}
    {label : Action → String}
    {observe : State → Observation}
    {presentation : Future.FutureEquivalencePresentation
      (Bridge.deterministicSystem step label) observe}
    (realization : CanonicalFutureDynamicalRealization
      step label observe presentation)
    (actions : List Action) (state : State) →
  Future.classOf presentation (Refinement.run step actions state)
  ≡ runQuotient realization actions (Future.classOf presentation state)
canonicalEncodingCommutesWithTrace realization [] state = refl
canonicalEncodingCommutesWithTrace
  {step = step} realization (action ∷ actions) state =
  trans
    (canonicalEncodingCommutesWithTrace realization actions (step action state))
    (cong (runQuotient realization actions)
      (actionDescends realization action state))

record SectionedFutureSafeRepresentation
    {State Action Observation Coarse : Set}
    {step : Action → State → State}
    {label : Action → String}
    {observe : State → Observation}
    (coarsen : State → Coarse) : Set₁ where
  constructor sectionedFutureSafeRepresentation
  field
    safe : Future.FutureLanguageSafeProjection
      (Bridge.deterministicSystem step label) observe coarsen
    coarseSectioned : Future.SectionedProjection coarsen

open SectionedFutureSafeRepresentation public

canonicalQuotientFactorsEverySectionedSafeRepresentation :
  ∀ {State Action Observation Coarse}
    {step : Action → State → State}
    {label : Action → String}
    {observe : State → Observation}
    {coarsen : State → Coarse}
    (presentation : Future.FutureEquivalencePresentation
      (Bridge.deterministicSystem step label) observe) →
  SectionedFutureSafeRepresentation
    {step = step} {label = label} {observe = observe} coarsen →
  Future.FactorizationThroughFutureQuotient presentation
canonicalQuotientFactorsEverySectionedSafeRepresentation presentation candidate =
  Future.sectionedSafeProjectionFactors
    presentation (safe candidate) (coarseSectioned candidate)

invariantRepresentationFactorsOntoCanonicalQuotient :
  ∀ {State Action Observation Latent}
    (representation :
      Invariant.FutureSufficientInvariantRepresentation
        State Action Observation Latent)
    (presentation : Future.FutureEquivalencePresentation
      (Bridge.deterministicSystem
        (Invariant.step representation)
        (Invariant.actionLabel representation))
      (Invariant.observe representation)) →
  Future.SectionedProjection (Invariant.encode representation) →
  Future.FactorizationThroughFutureQuotient presentation
invariantRepresentationFactorsOntoCanonicalQuotient
  representation presentation sectioned =
  Future.sectionedSafeProjectionFactors
    presentation
    (Invariant.invariantRepresentationIsFutureLanguageSafeProjection representation)
    sectioned

------------------------------------------------------------------------
-- What remains for a finite executable *linear-coordinate* compiler is to
-- search encodings of QuotientCode and optimize dimension/rate/geometry.  No
-- exact future-safe candidate may use a coarser state partition than this one.
------------------------------------------------------------------------
