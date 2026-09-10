module DASHI.Culture.McCaslandEventTimeApplicationTransformationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- MCCASLAND: HISTORICAL APPLICATION ROLE VS EVENT-TIME CONTINUITY
--
-- The old owner promoted a 2014 ATA appointment receipt under an event-time
-- module name.  A later primary USRA biography states that McCasland served as
-- ATA Chief Technology Officer from 2013-2021 and was, in 2023, an independent
-- consultant advising industry and government clients.  Therefore the ATA role
-- is source-backed historical capability evidence, but it cannot be inherited
-- into the 2025-2026 disappearance window without a dated continuity carrier.
--
-- No claim is made here that consulting work was sensitive, that a particular
-- client/programme existed at event time, or that any work caused the event.
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

mcCasland2025To2026EventTimeRole : ApplicationRoleReceipt
mcCasland2025To2026EventTimeRole = application-role-receipt
  "William Neil McCasland"
  "event-time employer/client/programme unresolved"
  "2025-2026 operational role not yet source-welded"
  "2025-2026 disappearance window"
  "requires dated employer/client/project responsibility evidence"
  "historical ATA/USAF roles may seed search but do not pay continuity"
  "no primary 2025-2026 employer/client/project carrier owned in this module"
  eventTimeRoleNotLocated
  false false false

-- Compatibility name retained for downstream imports, but it now denotes the
-- bounded historical ATA receipt rather than pretending that 2014 = event time.
mcCaslandATAApplicationRole : ApplicationRoleReceipt
mcCaslandATAApplicationRole = mcCaslandATAHistoricalRole

record McCaslandApplicationBoundary : Set where
  constructor mccasland-application-boundary
  field
    historicalATARoleEquals2026Role : Bool
    consultingState2023Equals2026ClientIdentity : Bool
    technologyStrategyRoleImpliesEveryProgrammePossession : Bool
    directedEnergyPortfolioImpliesUAPTechnology : Bool
    priorSAPOversightImpliesEventTimeSAPPossession : Bool
    eventTimeRoleSupportsExactProgrammeSearchOnlyAfterContinuity : Bool
    dated2025To2026EmployerClientCarrierStillRequired : Bool

open McCaslandApplicationBoundary public

canonicalMcCaslandApplicationBoundary : McCaslandApplicationBoundary
canonicalMcCaslandApplicationBoundary = mccasland-application-boundary
  false false false false false true true

data McCaslandApplicationReverseTarget : Set where
  acquire2025To2026EmployerOrClientIdentity : McCaslandApplicationReverseTarget
  acquireEventTimeProgrammeList : McCaslandApplicationReverseTarget
  acquireIRADOrTechnologyPortfolio : McCaslandApplicationReverseTarget
  acquireConfigurationOrIntegrationRole : McCaslandApplicationReverseTarget
  acquireProgrammeAccessReceipt : McCaslandApplicationReverseTarget
  acquireNamedSuccessorOrHandover : McCaslandApplicationReverseTarget
  acquireObserverOrReviewSurface : McCaslandApplicationReverseTarget

firstMcCaslandEventTimeTarget : McCaslandApplicationReverseTarget
firstMcCaslandEventTimeTarget = acquire2025To2026EmployerOrClientIdentity
