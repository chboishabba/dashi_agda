module DASHI.Governance.RequiredAxisAuthorityRoutingExact where

------------------------------------------------------------------------
-- REQUIRED-AXIS EVIDENCE -> ADMISSIBLE AUTHORITY ROUTE
--
-- Evidence resolution and semantic/normative routing obligations remain
-- distinct.  A support square never self-promotes into mandate, safety or
-- authority.  Instead an application supplies an interpretation explaining how
-- a resolved evidential axis discharges each RoutingSystem obligation.
--
-- This module then proves the constructive direction:
--   all required axes resolved + interpretation -> AdmissibleRoute.
--
-- Source calibration is inherited from the imported modules:
-- Belnap 1977 DOI 10.1007/978-94-010-1161-7_2 for the information square;
-- Pitkin 1967 (book; no DOI assigned) for scoped/recallable authority grammar;
-- Crenshaw 1991 DOI 10.2307/1229039 for situated non-collapse discipline.
-- The evidence-to-obligation interpretation is a DASHI construction.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.RequiredAxisSupportSquareExact as Support
import DASHI.Governance.JusticeRequiredAxisEvidenceExact as Evidence
import DASHI.Governance.MandateBackedAuthorityRoutingExact as MandateRouting
import DASHI.Governance.SituatedAuthorityRoutingExact as Routing

record RouteEvidenceInterpretation
    {Situation Route : Set}
    (system : Routing.RoutingSystem Situation Route)
    (situation : Situation)
    (route : Route)
    (profile : Evidence.RouteEvidenceProfile) : Set₁ where
  constructor routeEvidenceInterpretation
  field
    sufficiencyFromEvidence :
      Support.ResolvedPositive
        (Evidence.routeEvidenceAt profile Evidence.sufficiencyAxis) →
      Routing.Sufficient system situation route
    competenceFromEvidence :
      Support.ResolvedPositive
        (Evidence.routeEvidenceAt profile Evidence.competenceAxis) →
      Routing.Competent system situation route
    mandateFromEvidence :
      Support.ResolvedPositive
        (Evidence.routeEvidenceAt profile Evidence.mandateAxis) →
      Routing.Mandated system situation route
    currentAuthorityFromEvidence :
      Support.ResolvedPositive
        (Evidence.routeEvidenceAt profile Evidence.currentAuthorityAxis) →
      Routing.CurrentAuthority system situation route
    subjectLegibilityFromEvidence :
      Support.ResolvedPositive
        (Evidence.routeEvidenceAt profile Evidence.subjectLegibilityAxis) →
      Routing.SubjectLegible system situation route
    safetyFromEvidence :
      Support.ResolvedPositive
        (Evidence.routeEvidenceAt profile Evidence.safetyAxis) →
      Routing.Safe system situation route
    reviewabilityFromEvidence :
      Support.ResolvedPositive
        (Evidence.routeEvidenceAt profile Evidence.reviewabilityAxis) →
      Routing.Reviewable system situation route
    repairCapacityFromEvidence :
      Support.ResolvedPositive
        (Evidence.routeEvidenceAt profile Evidence.repairCapacityAxis) →
      Routing.RepairCapable system situation route

open RouteEvidenceInterpretation public

requiredAxisEvidenceYieldsAdmissibleRoute :
  ∀ {Situation Route}
    {system : Routing.RoutingSystem Situation Route}
    {situation : Situation}
    {route : Route}
    {profile : Evidence.RouteEvidenceProfile} →
  Support.RequiredAxesResolved (Evidence.routeEvidenceFamily profile) →
  RouteEvidenceInterpretation system situation route profile →
  Routing.AdmissibleRoute system situation route
requiredAxisEvidenceYieldsAdmissibleRoute resolved interpretation =
  Routing.admissibleRoute
    (sufficiencyFromEvidence interpretation
      (Support.resolveRequired resolved Evidence.sufficiencyAxis tt))
    (competenceFromEvidence interpretation
      (Support.resolveRequired resolved Evidence.competenceAxis tt))
    (mandateFromEvidence interpretation
      (Support.resolveRequired resolved Evidence.mandateAxis tt))
    (currentAuthorityFromEvidence interpretation
      (Support.resolveRequired resolved Evidence.currentAuthorityAxis tt))
    (subjectLegibilityFromEvidence interpretation
      (Support.resolveRequired resolved Evidence.subjectLegibilityAxis tt))
    (safetyFromEvidence interpretation
      (Support.resolveRequired resolved Evidence.safetyAxis tt))
    (reviewabilityFromEvidence interpretation
      (Support.resolveRequired resolved Evidence.reviewabilityAxis tt))
    (repairCapacityFromEvidence interpretation
      (Support.resolveRequired resolved Evidence.repairCapacityAxis tt))

------------------------------------------------------------------------
-- Exact inhabited constructive route.
------------------------------------------------------------------------

allPositiveRouteEvidence :
  Evidence.RoutingEvidenceAxis → Support.SupportSquare
allPositiveRouteEvidence axis = Support.supportSquare true false

allPositiveRouteEvidenceProfile : Evidence.RouteEvidenceProfile
allPositiveRouteEvidenceProfile =
  Evidence.routeEvidenceProfile allPositiveRouteEvidence

allPositiveRouteEvidenceResolved :
  Support.RequiredAxesResolved
    (Evidence.routeEvidenceFamily allPositiveRouteEvidenceProfile)
allPositiveRouteEvidenceResolved =
  Support.requiredAxesResolved
    (λ axis required → refl , refl)

canonicalRouteEvidenceInterpretation :
  RouteEvidenceInterpretation
    MandateRouting.demoRouting
    MandateRouting.delegatedResponseSituation
    MandateRouting.delegatedResponderRoute
    allPositiveRouteEvidenceProfile
canonicalRouteEvidenceInterpretation =
  routeEvidenceInterpretation
    (λ evidence → tt)
    (λ evidence → tt)
    (λ evidence → tt)
    (λ evidence → tt)
    (λ evidence → tt)
    (λ evidence → tt)
    (λ evidence → tt)
    (λ evidence → tt)

canonicalEvidenceDerivedAdmissibleRoute :
  Routing.AdmissibleRoute
    MandateRouting.demoRouting
    MandateRouting.delegatedResponseSituation
    MandateRouting.delegatedResponderRoute
canonicalEvidenceDerivedAdmissibleRoute =
  requiredAxisEvidenceYieldsAdmissibleRoute
    allPositiveRouteEvidenceResolved
    canonicalRouteEvidenceInterpretation

------------------------------------------------------------------------
-- Missing current-authority evidence blocks the constructive gate before an
-- interpretation can manufacture a route from unrelated positive evidence.
------------------------------------------------------------------------

formerSupporterEvidenceCannotDischargeAllRoutingAxes :
  Support.RequiredAxesResolved
    (Evidence.routeEvidenceFamily Evidence.formerSupporterEvidenceProfile) →
  ⊥
formerSupporterEvidenceCannotDischargeAllRoutingAxes =
  Evidence.pooledRoutingEvidenceCannotManufactureCurrentAuthority

record RequiredAxisAuthorityRoutingBoundary : Set where
  constructor requiredAxisAuthorityRoutingBoundary
  field
    supportSquareSelfPromotesToAuthority : Bool
    interpretationRequiredToDischargeRoutingObligations : Bool
    allResolvedAxesCanConstructAdmissibleRouteUnderInterpretation : Bool
    unrelatedPositiveEvidenceCanFillMissingCurrentAuthority : Bool

canonicalRequiredAxisAuthorityRoutingBoundary :
  RequiredAxisAuthorityRoutingBoundary
canonicalRequiredAxisAuthorityRoutingBoundary =
  requiredAxisAuthorityRoutingBoundary false true true false
