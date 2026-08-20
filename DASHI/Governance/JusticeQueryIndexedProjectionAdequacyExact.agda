module DASHI.Governance.JusticeQueryIndexedProjectionAdequacyExact where

------------------------------------------------------------------------
-- QUERY-INDEXED ADEQUACY FOR THE SAME INCIDENT PROJECTION
--
-- The same coarse incident projection can be perfectly adequate for reporting
-- its own public surface and inadequate for selecting a situated responder.
-- Adequacy is therefore indexed by the query / intervention language, not an
-- intrinsic Boolean property of the projection.
--
-- Source calibration inherited from the generic core:
-- David Blackwell, "Equivalent Comparisons of Experiments",
-- Annals of Mathematical Statistics 24(2), 265-272 (1953).
-- DOI: 10.1214/aoms/1177729032.
--
-- Dynamic refinements remain governed separately by
-- FutureObservationalRefinement / DynamicalQuotientSafety; this module does not
-- collapse static query factorisation into future trace safety.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Adequacy
import DASHI.Governance.AuthorityRoutingProjectionSafetyExact as Projection
import DASHI.Governance.SituatedAuthorityRoutingExact as Routing


data IncidentQuery : Set where
  publicSurfaceQuery responderRoutingQuery : IncidentQuery

data IncidentQueryAnswer : Set where
  surfaceAnswer : Projection.CoarseIncident → IncidentQueryAnswer
  routeAnswer : Routing.DemoRoute → IncidentQueryAnswer

incidentQueryAnswer :
  IncidentQuery → Projection.FineIncident → IncidentQueryAnswer
incidentQueryAnswer publicSurfaceQuery incident =
  surfaceAnswer (Projection.incidentProjection incident)
incidentQueryAnswer responderRoutingQuery incident =
  routeAnswer (Projection.requiredRoute incident)

incidentQuerySemantics :
  Adequacy.QuerySemantics
    Projection.FineIncident
    IncidentQuery
    IncidentQueryAnswer
incidentQuerySemantics = Adequacy.querySemantics incidentQueryAnswer

publicSurfaceQueryIsAdequate :
  Adequacy.AdequateFor
    Projection.incidentProjection
    incidentQuerySemantics
    publicSurfaceQuery
publicSurfaceQueryIsAdequate =
  Adequacy.factorsForQuery
    surfaceAnswer
    (λ incident → refl)

responderRoutingQueryDefect :
  Adequacy.QueryAdequacyDefect
    Projection.incidentProjection
    incidentQuerySemantics
    responderRoutingQuery
responderRoutingQueryDefect =
  Adequacy.queryAdequacyDefect
    Projection.distressIncident
    Projection.imminentThreatIncident
    refl
    (λ ())

responderRoutingQueryIsNotAdequate :
  Adequacy.AdequateFor
    Projection.incidentProjection
    incidentQuerySemantics
    responderRoutingQuery →
  ⊥
responderRoutingQueryIsNotAdequate =
  Adequacy.queryAdequacyDefectBlocksFactorisation
    responderRoutingQueryDefect

record SameProjectionDifferentJusticeQueryAdequacy : Set₁ where
  constructor sameProjectionDifferentJusticeQueryAdequacy
  field
    adequateForPublicSurface :
      Adequacy.AdequateFor
        Projection.incidentProjection
        incidentQuerySemantics
        publicSurfaceQuery
    routingDefect :
      Adequacy.QueryAdequacyDefect
        Projection.incidentProjection
        incidentQuerySemantics
        responderRoutingQuery

open SameProjectionDifferentJusticeQueryAdequacy public

sameIncidentProjectionAdequateForSurfaceNotRouting :
  SameProjectionDifferentJusticeQueryAdequacy
sameIncidentProjectionAdequateForSurfaceNotRouting =
  sameProjectionDifferentJusticeQueryAdequacy
    publicSurfaceQueryIsAdequate
    responderRoutingQueryDefect

record JusticeQueryIndexedProjectionBoundary : Set where
  constructor justiceQueryIndexedProjectionBoundary
  field
    publicSurfaceAdequacyImpliesRoutingAdequacy : Bool
    sameProjectionMayHaveDifferentQueryAdequacy : Bool
    routingAdequacyRequiresFineRouteConstancyOnFibres : Bool
    staticQueryAdequacyAutomaticallyProvesDynamicSafety : Bool

canonicalJusticeQueryIndexedProjectionBoundary :
  JusticeQueryIndexedProjectionBoundary
canonicalJusticeQueryIndexedProjectionBoundary =
  justiceQueryIndexedProjectionBoundary false true true false
