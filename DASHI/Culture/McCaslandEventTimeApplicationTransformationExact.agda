module DASHI.Culture.McCaslandEventTimeApplicationTransformationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- MCCASLAND: HISTORICAL APPLICATION ROLE VS EVENT-TIME CONTINUITY
------------------------------------------------------------------------

data TemporalRoleStatus : Set where
  historicalRoleSourceBacked : TemporalRoleStatus
  eventTimeContinuityPartial : TemporalRoleStatus
  eventTimeRoleNotLocated : TemporalRoleStatus

record ApplicationRoleReceipt : Set where
  constructor application-role-receipt
  field
    person : String
    organisationOrWorkMode : String
    role : String
    timeWindow : String
    transformationResponsibility : String
    publicApplicationSurface : String
    sourceReference : String
    temporalStatus : TemporalRoleStatus
    roleIdentityOwned : Bool
    exact2025To2026ContinuityOwned : Bool
    exactProgrammeCarrierOwned : Bool

open ApplicationRoleReceipt public

mcCaslandATAHistoricalRole : ApplicationRoleReceipt
mcCaslandATAHistoricalRole = application-role-receipt
  "William Neil McCasland"
  "Applied Technology Associates"
  "technology leadership / Chief Technology Officer; earlier appointment language used Director of Technology"
  "2013-2021 CTO tenure according to 2023 USRA primary biography; 2014 appointment announcement is an earlier role carrier"
  "technology identification/development, technical vision and strategy"
  "ATA public portfolio included space-vehicle, target acquisition/tracking and other precision-technology programmes"
  "Universities Space Research Association organizational biography (2023); Applied Technology Associates appointment announcement (2014)"
  historicalRoleSourceBacked
  true false false

mcCasland2023ConsultingState : ApplicationRoleReceipt
mcCasland2023ConsultingState = application-role-receipt
  "William Neil McCasland"
  "independent consulting"
  "independent consultant advising industry and government clients"
  "2023 biography state"
  "client-specific responsibility not identified by this carrier"
  "USRA biography exposes consulting status, not a client or application object"
  "Universities Space Research Association organizational biography (2023)"
  eventTimeContinuityPartial
  true false false

------------------------------------------------------------------------
-- DBE Consulting lead.
--
-- The Kirtland Partnership Committee's own board page currently labels
-- McCasland "Founder, Owner, and President, DBE Consulting LLC".  The same page
-- body also contains stale ATA Director-of-Technology prose, so the DBE heading
-- is a primary organizational lead for his post-ATA work mode, not yet a dated
-- 2025-2026 corporate-filing receipt or a client/programme identity.
------------------------------------------------------------------------

mcCaslandDBEConsultingLead : ApplicationRoleReceipt
mcCaslandDBEConsultingLead = application-role-receipt
  "William Neil McCasland"
  "DBE Consulting LLC"
  "Founder, Owner, and President"
  "post-ATA work-mode lead; exact effective dates not paid by the located Kirtland Partnership Committee page"
  "independent consulting work; exact client/project responsibility not identified"
  "Kirtland Partnership Committee board surface carries the DBE role heading but also stale ATA biography text"
  "Kirtland Partnership Committee board page for Neil McCasland"
  eventTimeContinuityPartial
  true false false

mcCasland2025To2026EventTimeRole : ApplicationRoleReceipt
mcCasland2025To2026EventTimeRole = application-role-receipt
  "William Neil McCasland"
  "DBE Consulting LLC / exact event-time client or programme unresolved"
  "post-ATA consulting work mode partially identified; 2025-2026 operational client/project not yet source-welded"
  "2025-2026 disappearance window"
  "requires dated DBE corporate-status evidence and client/project responsibility evidence"
  "USRA 2025 governance role and Kirtland Partnership Committee DBE heading may seed search but do not pay a technical application object"
  "USRA 2025 Board of Trustees; Kirtland Partnership Committee DBE Consulting heading"
  eventTimeContinuityPartial
  true false false

mcCaslandATAApplicationRole : ApplicationRoleReceipt
mcCaslandATAApplicationRole = mcCaslandATAHistoricalRole

record McCaslandApplicationBoundary : Set where
  constructor mccasland-application-boundary
  field
    historicalATARoleEquals2026Role : Bool
    consultingState2023Equals2026ClientIdentity : Bool
    kpcDBEHeadingEqualsDated2026CorporateStatus : Bool
    dbeRoleEqualsExactClientProgrammeIdentity : Bool
    technologyStrategyRoleImpliesEveryProgrammePossession : Bool
    directedEnergyPortfolioImpliesUAPTechnology : Bool
    priorSAPOversightImpliesEventTimeSAPPossession : Bool
    eventTimeRoleSupportsExactProgrammeSearchOnlyAfterContinuity : Bool
    dated2025To2026EmployerClientCarrierStillRequired : Bool

open McCaslandApplicationBoundary public

canonicalMcCaslandApplicationBoundary : McCaslandApplicationBoundary
canonicalMcCaslandApplicationBoundary = mccasland-application-boundary
  false false false false false false false true true

data McCaslandApplicationReverseTarget : Set where
  acquireDBECorporateEffectiveDateAndStatus : McCaslandApplicationReverseTarget
  acquire2025To2026EmployerOrClientIdentity : McCaslandApplicationReverseTarget
  acquireEventTimeProgrammeList : McCaslandApplicationReverseTarget
  acquireIRADOrTechnologyPortfolio : McCaslandApplicationReverseTarget
  acquireConfigurationOrIntegrationRole : McCaslandApplicationReverseTarget
  acquireProgrammeAccessReceipt : McCaslandApplicationReverseTarget
  acquireNamedSuccessorOrHandover : McCaslandApplicationReverseTarget
  acquireObserverOrReviewSurface : McCaslandApplicationReverseTarget

firstMcCaslandEventTimeTarget : McCaslandApplicationReverseTarget
firstMcCaslandEventTimeTarget = acquireDBECorporateEffectiveDateAndStatus
