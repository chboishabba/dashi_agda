module DASHI.Cognition.PNF.CanonicalFutureMinimalDynamicalRealizationExact where

------------------------------------------------------------------------
-- CANONICAL FUTURE QUOTIENT -> MINIMAL DYNAMICAL REALIZATION
--
-- The canonical future quotient already answers which fine states may coincide.
-- The missing dynamical theorem is that deterministic actions descend to that
-- quotient.  Once a representative/section is supplied, every action induces a
-- well-defined quotient action, and every sectioned future-safe representation
-- factors onto the canonical quotient.  This is minimality in the information /
-- quotient order, not yet minimum vector-space dimension.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.FutureObservationLanguageQuotientExact as Future
import DASHI.Core.StablePartitionCanonicalFutureBridgeExact as Bridge
import DASHI.Cognition.PNF.FutureSufficientInvariantSubspaceExact as Invariant

------------------------------------------------------------------------
-- Future equivalence is a congruence for every deterministic action.
------------------------------------------------------------------------

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
    sectioned : Future.SectionedProjection (Future.classOf presentation)
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
      _ → Future.QuotientCode presentation → Future.QuotientCode presentation
    quotientStep action code =
      Future.classOf presentation
        (step action (Future.section sectioned code))

    proof : (action : _) (state : _) →
      Future.classOf presentation (step action state)
      ≡ quotientStep action (Future.classOf presentation state)
    proof action state =
      Future.classEqualityComplete presentation
        (futureEquivalentStepCongruence
          (Future.classEqualitySound presentation
            (sym (Future.sectionRightInverse sectioned
              (Future.classOf presentation state))))
          action)

------------------------------------------------------------------------
-- Quotient dynamics commute with the canonical encoder through arbitrary
-- finite action traces.
------------------------------------------------------------------------

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
  Future.classOf presentation
    (DASHI.Core.GenericFuturePartitionRefinementExact.run step actions state)
  ≡ runQuotient realization actions (Future.classOf presentation state)
canonicalEncodingCommutesWithTrace realization [] state = refl
canonicalEncodingCommutesWithTrace
  {step = step} realization (action ∷ actions) state =
  trans
    (canonicalEncodingCommutesWithTrace realization actions (step action state))
    (cong (runQuotient realization actions)
      (actionDescends realization action state))

------------------------------------------------------------------------
-- MINIMALITY THEOREM
--
-- Any sectioned representation whose kernel is future-safe admits a map onto
-- the canonical quotient.  Thus it cannot identify two distinct canonical
-- future classes.  The canonical quotient is the coarsest exact realization in
-- this factorization order.
------------------------------------------------------------------------

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
    sectioned : Future.SectionedProjection coarsen

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
    presentation (safe candidate) (sectioned candidate)

------------------------------------------------------------------------
-- Direct bridge from the invariant-representation theorem: if a dynamics-
-- closed representation has a section, it necessarily factors onto the
-- canonical future quotient.
------------------------------------------------------------------------

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
-- This is the promised canonical-future-quotient -> minimal dynamical
-- realization theorem.  What remains for a finite executable "linear realization
-- compiler" is to choose/search an algebraic coordinate system for QuotientCode
-- and optimize its dimension/rate/geometry.  That optimization cannot make a
-- coarser exact state partition than the canonical quotient proved here.
------------------------------------------------------------------------
