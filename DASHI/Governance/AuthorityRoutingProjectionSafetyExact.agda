module DASHI.Governance.AuthorityRoutingProjectionSafetyExact where

------------------------------------------------------------------------
-- AUTHORITY ROUTING UNDER LOSSY / DYNAMIC PROJECTION
--
-- A routing observer is sufficient only if distinctions erased by the
-- projection are irrelevant to the route and to the future consequences of
-- policy-selected actions.  The module reuses existing non-factorability,
-- policy-relative safety, plural-consumer safety, and future-observational
-- refinement cores rather than inventing a parallel observer theory.
--
-- Mathematical ancestor retained by the reused future-refinement core:
-- Ugo Montanari and Vladimiro Sassone,
-- "Dynamic Congruence vs. Progressing Bisimulation for CCS",
-- Fundamenta Informaticae 16(2), 1992.
-- DOI: 10.3233/FI-1992-16206.
--
-- Intersectional carrier motivation:
-- Kimberle Williams Crenshaw, "Mapping the Margins: Intersectionality,
-- Identity Politics, and Violence against Women of Color" (1991).
-- DOI: 10.2307/1229039.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.DynamicalQuotientSafety as Dynamic
import DASHI.Core.FutureObservationalRefinement as Future
import DASHI.Core.IntersectionalNonFactorability as NonFactor
import DASHI.Core.PluralConsumerProjectionSafety as Plural
import DASHI.Core.PolicyRelativeProjectionSafety as Policy
import DASHI.Core.TypedDependencyCore as Dependency
import DASHI.Governance.SituatedAuthorityRoutingExact as Routing
import DASHI.Reasoning.RelationalChronologyProjectionBoundary as Chronology

------------------------------------------------------------------------
-- Generic theorem: an explicit collision with different required routes rules
-- out every router that factors only through the coarse observer.
------------------------------------------------------------------------

RoutingFactorisation :
  ∀ {Situation Observation Route : Set} →
  (Situation → Observation) →
  (Situation → Route) →
  Set₁
RoutingFactorisation = NonFactor.FactorsThrough

record RoutingObserverDefect
    {Situation Observation Route : Set}
    (project : Situation → Observation)
    (route : Situation → Route) : Set₁ where
  constructor routingObserverDefect
  field
    nonFactorability : NonFactor.NonFactorabilityWitness project route

open RoutingObserverDefect public

ObserverInsufficiencyBlocksSoundAuthorityRouting :
  ∀ {Situation Observation Route}
    {project : Situation → Observation}
    {route : Situation → Route} →
  RoutingObserverDefect project route →
  RoutingFactorisation project route →
  ⊥
ObserverInsufficiencyBlocksSoundAuthorityRouting defect factor =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (nonFactorability defect)
    factor

------------------------------------------------------------------------
-- Concrete "disturbance" collision: the public incident surface is identical,
-- but one fine state routes to a clinician and the other to police.
------------------------------------------------------------------------

data FineIncident : Set where
  distressIncident imminentThreatIncident : FineIncident

data CoarseIncident : Set where
  disturbanceSurface : CoarseIncident

incidentProjection : FineIncident → CoarseIncident
incidentProjection distressIncident = disturbanceSurface
incidentProjection imminentThreatIncident = disturbanceSurface

requiredRoute : FineIncident → Routing.DemoRoute
requiredRoute distressIncident = Routing.clinicianRoute
requiredRoute imminentThreatIncident = Routing.policeRoute

requiredRoutesDiffer :
  requiredRoute distressIncident ≡ requiredRoute imminentThreatIncident →
  ⊥
requiredRoutesDiffer ()

canonicalRoutingObserverDefect :
  RoutingObserverDefect incidentProjection requiredRoute
canonicalRoutingObserverDefect =
  routingObserverDefect
    (NonFactor.nonFactorabilityWitness
      distressIncident
      imminentThreatIncident
      refl
      requiredRoutesDiffer)

incidentLabelCannotDetermineSoundRoute :
  RoutingFactorisation incidentProjection requiredRoute →
  ⊥
incidentLabelCannotDetermineSoundRoute =
  ObserverInsufficiencyBlocksSoundAuthorityRouting
    canonicalRoutingObserverDefect

------------------------------------------------------------------------
-- Causal-order loss can itself change the selected route.
-- This is an exact finite countermodel; it does not assert that any live
-- incident actually instantiates the reversed chronology.
------------------------------------------------------------------------

routeByChronology : Chronology.ChronologyShape → Routing.DemoRoute
routeByChronology Chronology.actImpactObjectionResponseShape =
  Routing.elderCommunityRoute
routeByChronology Chronology.objectionDistressBlameShape =
  Routing.policeRoute

CausalOrderLossCanChangeAdmissibleResponder :
  routeByChronology Chronology.actImpactObjectionResponseShape
  ≡
  routeByChronology Chronology.objectionDistressBlameShape →
  ⊥
CausalOrderLossCanChangeAdmissibleResponder ()

causalOrderProjectionIsLossy :
  Chronology.sourceShape Chronology.canonicalCausalOrderLoss
  ≡ Chronology.actImpactObjectionResponseShape
  ×
  Chronology.projectedShape Chronology.canonicalCausalOrderLoss
  ≡ Chronology.objectionDistressBlameShape
causalOrderProjectionIsLossy = refl , refl

------------------------------------------------------------------------
-- Adjudicated records are likewise too coarse to reconstruct total lived
-- relational state.
------------------------------------------------------------------------

adjudicatedRecordDoesNotDetermineLivedJusticeState :
  Chronology.AdjudicatedRecordDeterminesTotalIdentity →
  ⊥
adjudicatedRecordDoesNotDetermineLivedJusticeState =
  Chronology.adjudicatedRecordDoesNotDetermineTotalIdentity

------------------------------------------------------------------------
-- Dynamic and policy-relative safety bridges.
------------------------------------------------------------------------

unsafeLegibilityProjectionBlocksSafeInterventionLoop :
  ∀ {State Action Observation}
    {system : Dependency.DependentActionSystem State Action}
    {project : State → Observation}
    {policy : Policy.CoarseInterventionPolicy Observation Action} →
  Policy.PolicyRelativeSafety system project policy →
  Policy.PolicyExposedQuotientDefect system project policy →
  ⊥
unsafeLegibilityProjectionBlocksSafeInterventionLoop =
  Policy.policyDefectContradictsPolicySafety

dynamicSafetyPromotesCurrentRoutingEquivalenceToFuture :
  ∀ {State Action Observation}
    {system : Dependency.DependentActionSystem State Action}
    {project : State → Observation} →
  Dynamic.DynamicConsumerSafety system project →
  ∀ {left right} →
  Future.CurrentEquivalent project left right →
  Future.FutureEquivalent system project left right
dynamicSafetyPromotesCurrentRoutingEquivalenceToFuture =
  Future.dynamicSafetyExactlyPromotesCurrentToFuture

boundedObserverSafetyDoesNotEstablishAffectedPersonSafety :
  Plural.PluralDynamicSafety Plural.canonicalDemoProjectionFamily →
  ⊥
boundedObserverSafetyDoesNotEstablishAffectedPersonSafety =
  Plural.boundedSafetyDoesNotYieldPluralSafety

------------------------------------------------------------------------
-- The existing FutureEquivalent relation is already the greatest dynamically
-- congruent refinement of a current projection.  Expose it here as the
-- canonical refinement target for justice routing.
------------------------------------------------------------------------

routingUsesCanonicalMaximalSafeRefinement :
  ∀ {State Action Observation}
    (system : Dependency.DependentActionSystem State Action)
    (project : State → Observation) →
  Future.MaximalSafeRefinement system project
routingUsesCanonicalMaximalSafeRefinement =
  Future.canonicalMaximalSafeRefinement

record AuthorityRoutingProjectionBoundary : Set where
  constructor authorityRoutingProjectionBoundary
  field
    coarseIncidentLabelDeterminesRoute : Bool
    currentEqualityGuaranteesFutureEqualityWithoutSafety : Bool
    oneConsumerSafetyPromotesToPluralSafety : Bool
    adjudicatedRecordRecoversTotalLivedState : Bool
    routingMustRespectFutureRelevantDistinctions : Bool

canonicalAuthorityRoutingProjectionBoundary :
  AuthorityRoutingProjectionBoundary
canonicalAuthorityRoutingProjectionBoundary =
  authorityRoutingProjectionBoundary false false false false true
