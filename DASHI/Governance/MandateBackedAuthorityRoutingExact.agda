module DASHI.Governance.MandateBackedAuthorityRoutingExact where

------------------------------------------------------------------------
-- MANDATE-BACKED SITUATED AUTHORITY ROUTING
--
-- SituatedAuthorityRoutingExact keeps mandate/current-authority proof-bearing
-- but application-generic.  AuthorityMandateCore already owns the stronger
-- public-authority carrier: admissible source, constituency relation, explicit
-- scope, recall and review.  This module welds those layers without allowing
-- role or force possession to mint authority.
--
-- Conceptual precedent inherited from AuthorityMandateCore:
-- Hanna Fenichel Pitkin, The Concept of Representation (1967).
-- Book; no DOI assigned.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Governance.AuthorityMandateCore as Authority
import DASHI.Governance.SituatedAuthorityRoutingExact as Routing

record RouteMandateInterpretation
    {Situation Route : Set}
    (mandate : Authority.Mandate) : Set₁ where
  constructor routeMandateInterpretation
  field
    constituencyFor : Situation → Authority.Constituency mandate
    representativeFor : Route → Authority.Representative mandate
    scopeFor : Situation → Route → Authority.Scope mandate

open RouteMandateInterpretation public

record MandateBackedAdmissibleRoute
    {Situation Route : Set}
    (routing : Routing.RoutingSystem Situation Route)
    (mandate : Authority.Mandate)
    (interpretation : RouteMandateInterpretation mandate)
    (situation : Situation)
    (route : Route) : Set₁ where
  constructor mandateBackedAdmissibleRoute
  field
    admissibleRoute : Routing.AdmissibleRoute routing situation route
    scopedAuthority : Authority.ScopedAuthority mandate
    constituencyMatches :
      Authority.constituency scopedAuthority
      ≡ constituencyFor interpretation situation
    representativeMatches :
      Authority.representative scopedAuthority
      ≡ representativeFor interpretation route
    scopeMatches :
      Authority.scope scopedAuthority
      ≡ scopeFor interpretation situation route

open MandateBackedAdmissibleRoute public

mandateBackedRouteCarriesRecallAndReview :
  ∀ {Situation Route}
    {routing : Routing.RoutingSystem Situation Route}
    {mandate : Authority.Mandate}
    {interpretation : RouteMandateInterpretation mandate}
    {situation : Situation}
    {route : Route} →
  (backed :
    MandateBackedAdmissibleRoute
      routing mandate interpretation situation route) →
  Authority.recallable mandate
    (Authority.constituency (scopedAuthority backed))
    (Authority.representative (scopedAuthority backed))
  ×
  Authority.reviewable mandate
    (Authority.representative (scopedAuthority backed))
mandateBackedRouteCarriesRecallAndReview backed =
  Authority.recallWitness (scopedAuthority backed)
  , Authority.reviewWitness (scopedAuthority backed)

mandateBackedRouteCarriesExplicitScope :
  ∀ {Situation Route}
    {routing : Routing.RoutingSystem Situation Route}
    {mandate : Authority.Mandate}
    {interpretation : RouteMandateInterpretation mandate}
    {situation : Situation}
    {route : Route} →
  (backed :
    MandateBackedAdmissibleRoute
      routing mandate interpretation situation route) →
  Authority.authorisedFor mandate
    (Authority.representative (scopedAuthority backed))
    (Authority.scope (scopedAuthority backed))
mandateBackedRouteCarriesExplicitScope backed =
  Authority.scopeWitness (scopedAuthority backed)

possessionOfForceCannotBackMandateRoute :
  ∀ {Situation Route}
    {routing : Routing.RoutingSystem Situation Route}
    {mandate : Authority.Mandate}
    {interpretation : RouteMandateInterpretation mandate}
    {situation : Situation}
    {route : Route} →
  (backed :
    MandateBackedAdmissibleRoute
      routing mandate interpretation situation route) →
  Authority.source (scopedAuthority backed) ≡ Authority.possessionOfForce →
  ⊥
possessionOfForceCannotBackMandateRoute backed refl =
  Authority.possessionOfForceRejected
    (Authority.sourceAdmissible (scopedAuthority backed))

record RouteAuthorityIsDiachronicallyScoped
    {Situation Route : Set}
    (routing : Routing.RoutingSystem Situation Route)
    (mandate : Authority.Mandate)
    (interpretation : RouteMandateInterpretation mandate)
    (situation : Situation)
    (route : Route) : Set₁ where
  constructor routeAuthorityIsDiachronicallyScoped
  field
    backed :
      MandateBackedAdmissibleRoute
        routing mandate interpretation situation route
    scopeWitnessRetained :
      Authority.authorisedFor mandate
        (Authority.representative (scopedAuthority backed))
        (Authority.scope (scopedAuthority backed))
    recallWitnessRetained :
      Authority.recallable mandate
        (Authority.constituency (scopedAuthority backed))
        (Authority.representative (scopedAuthority backed))
    reviewWitnessRetained :
      Authority.reviewable mandate
        (Authority.representative (scopedAuthority backed))

open RouteAuthorityIsDiachronicallyScoped public

mandateBackedRouteYieldsBoundedAuthority :
  ∀ {Situation Route}
    {routing : Routing.RoutingSystem Situation Route}
    {mandate : Authority.Mandate}
    {interpretation : RouteMandateInterpretation mandate}
    {situation : Situation}
    {route : Route} →
  (backed :
    MandateBackedAdmissibleRoute
      routing mandate interpretation situation route) →
  RouteAuthorityIsDiachronicallyScoped
    routing mandate interpretation situation route
mandateBackedRouteYieldsBoundedAuthority backed =
  routeAuthorityIsDiachronicallyScoped
    backed
    (Authority.scopeWitness (scopedAuthority backed))
    (Authority.recallWitness (scopedAuthority backed))
    (Authority.reviewWitness (scopedAuthority backed))

------------------------------------------------------------------------
-- Concrete inhabited witness: the bridge is not merely a negative boundary.
-- One situated route carries an admissible constitutional delegation plus
-- explicit representation, scope, recall and review witnesses.
------------------------------------------------------------------------

data DemoSituation : Set where
  delegatedResponseSituation : DemoSituation

data DemoRoute : Set where
  delegatedResponderRoute : DemoRoute

demoMandate : Authority.Mandate
demoMandate = record
  { Constituency = ⊤
  ; Representative = ⊤
  ; Scope = ⊤
  ; Term = ⊤
  ; representedBy = λ constituency representative → ⊤
  ; authorisedFor = λ representative scope → ⊤
  ; termOf = λ representative → tt
  ; recallable = λ constituency representative → ⊤
  ; reviewable = λ representative → ⊤
  }

demoRouting : Routing.RoutingSystem DemoSituation DemoRoute
demoRouting = record
  { Routing.Sufficient = λ situation route → ⊤
  ; Routing.Competent = λ situation route → ⊤
  ; Routing.Mandated = λ situation route → ⊤
  ; Routing.CurrentAuthority = λ situation route → ⊤
  ; Routing.SubjectLegible = λ situation route → ⊤
  ; Routing.Safe = λ situation route → ⊤
  ; Routing.Reviewable = λ situation route → ⊤
  ; Routing.RepairCapable = λ situation route → ⊤
  ; Routing.dominationCost = λ situation route → 0
  }

demoInterpretation : RouteMandateInterpretation demoMandate
demoInterpretation =
  routeMandateInterpretation
    (λ situation → tt)
    (λ route → tt)
    (λ situation route → tt)

demoAdmissibleRoute :
  Routing.AdmissibleRoute
    demoRouting delegatedResponseSituation delegatedResponderRoute
demoAdmissibleRoute =
  Routing.admissibleRoute tt tt tt tt tt tt tt tt

demoScopedAuthority : Authority.ScopedAuthority demoMandate
demoScopedAuthority = record
  { Authority.source = Authority.constitutionalDelegation
  ; Authority.sourceAdmissible = tt
  ; Authority.constituency = tt
  ; Authority.representative = tt
  ; Authority.scope = tt
  ; Authority.representationWitness = tt
  ; Authority.scopeWitness = tt
  ; Authority.recallWitness = tt
  ; Authority.reviewWitness = tt
  }

canonicalMandateBackedRoute :
  MandateBackedAdmissibleRoute
    demoRouting
    demoMandate
    demoInterpretation
    delegatedResponseSituation
    delegatedResponderRoute
canonicalMandateBackedRoute =
  mandateBackedAdmissibleRoute
    demoAdmissibleRoute
    demoScopedAuthority
    refl refl refl

canonicalMandateBackedRouteIsBounded :
  RouteAuthorityIsDiachronicallyScoped
    demoRouting
    demoMandate
    demoInterpretation
    delegatedResponseSituation
    delegatedResponderRoute
canonicalMandateBackedRouteIsBounded =
  mandateBackedRouteYieldsBoundedAuthority canonicalMandateBackedRoute

record MandateBackedRoutingBoundary : Set where
  constructor mandateBackedRoutingBoundary
  field
    routeRoleAloneCreatesMandate : Bool
    possessionOfForceCanBackScopedAuthority : Bool
    scopedAuthorityRequiresScope : Bool
    scopedAuthorityRequiresRecall : Bool
    scopedAuthorityRequiresReview : Bool
    inhabitedScopedRouteWitnessAvailable : Bool

canonicalMandateBackedRoutingBoundary : MandateBackedRoutingBoundary
canonicalMandateBackedRoutingBoundary =
  mandateBackedRoutingBoundary false false true true true true
