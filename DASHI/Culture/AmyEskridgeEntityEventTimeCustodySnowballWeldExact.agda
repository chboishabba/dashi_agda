module DASHI.Culture.AmyEskridgeEntityEventTimeCustodySnowballWeldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Culture.AmyEskridgeInstituteEntityContinuityExact as Entity
import DASHI.Culture.AmyEskridgeInstitutePostDeathContinuityExact as PostDeath
import DASHI.Culture.MissingDeceasedCustodyEventTimeMatrixExact as Matrix
import DASHI.Culture.AmyEskridgeInstituteTeamSECContinuitySnowballWeldExact as Role
import DASHI.Culture.AmyEskridgePOAMSApplicationCustodySnowballWeldExact as POAMS

------------------------------------------------------------------------
-- AMY ESKRIDGE MEMORIAL: ENTITY / EVENT-TIME / CUSTODY SNOWBALL WELD
--
-- Existing owners already establish a multi-year Institute entity surface and
-- a post-death corporate-entity surface.  This adapter composes those receipts
-- with the comparative custody/event-time matrix without promoting corporate
-- continuity into technical-carrier continuity.
------------------------------------------------------------------------

institute2019CorporateSurfaceOwned :
  Entity.secCorporateSurfaceOwned Entity.instituteEntityContinuity ≡ true
institute2019CorporateSurfaceOwned = refl

institute2020EntitySurfaceOwned :
  Entity.ppp2020EntitySurfaceOwned Entity.instituteEntityContinuity ≡ true
institute2020EntitySurfaceOwned = refl

institute2021EntitySurfaceOwned :
  Entity.ppp2021EntitySurfaceOwned Entity.instituteEntityContinuity ≡ true
institute2021EntitySurfaceOwned = refl

amy2018To2019InstitutionalContinuityPaid :
  Role.personInstitutionalContinuity2018To2019Paid
    Role.amy2018To2019InstitutionalContinuityFrontier ≡ true
amy2018To2019InstitutionalContinuityPaid = refl

amyEventTimeRoleStillPartial :
  Matrix.eventTimeRole Matrix.eskridgeRow ≡ Matrix.partial
amyEventTimeRoleStillPartial = refl

amyPhysicalCustodyStillNotLocated :
  Matrix.physicalCustody Matrix.eskridgeRow ≡ Matrix.notLocated
amyPhysicalCustodyStillNotLocated = refl

amyDigitalCustodyStillNotLocated :
  Matrix.digitalOrDataCustody Matrix.eskridgeRow ≡ Matrix.notLocated
amyDigitalCustodyStillNotLocated = refl

amyOrganisationalContinuityAlreadyPartial :
  Matrix.organisationalContinuity Matrix.eskridgeRow ≡ Matrix.partial
amyOrganisationalContinuityAlreadyPartial = refl

amySameCarrierSuccessionStillNotLocated :
  Matrix.sameCarrierSuccession Matrix.eskridgeRow ≡ Matrix.notLocated
amySameCarrierSuccessionStillNotLocated = refl

poamsExactInstituteDerivativeStillUnpaid :
  POAMS.exactInstituteDerivativeIdentityPaid POAMS.currentComposedPOAMSFrontier ≡ false
poamsExactInstituteDerivativeStillUnpaid = refl

record EntityEventTimeCustodyBoundary : Set where
  constructor entity-event-time-custody-boundary
  field
    multiYearEntitySurfaceMayPayOrganisationalContinuity : Bool
    postDeathEntitySurfaceMayExtendOrganisationalChronology : Bool
    entityContinuityPaysExactEventTimeRole : Bool
    entityContinuityPaysPhysicalCustody : Bool
    entityContinuityPaysDigitalCustody : Bool
    postDeathEntitySurvivalPaysTechnicalCarrierSurvival : Bool
    postDeathEntitySurvivalPaysSameCarrierSuccession : Bool
    samePersonRoleContinuityPaysSameExperimentContinuity : Bool
    corporateContinuityCreatesDeathCausation : Bool

open EntityEventTimeCustodyBoundary public

canonicalEntityEventTimeCustodyBoundary : EntityEventTimeCustodyBoundary
canonicalEntityEventTimeCustodyBoundary =
  entity-event-time-custody-boundary
    true true false false false false false false false

------------------------------------------------------------------------
-- Current composed reading:
--
--  * Institute corporate/entity continuity is source-backed across 2019-2021;
--  * a post-death Institute entity surface is retained;
--  * Amy's person/institutional continuity is paid through 2019;
--  * event-time technical role remains partial;
--  * physical/digital custody and same-carrier succession remain unlocated;
--  * exact Institute derivative identity remains the first application-carrier
--    identity leaf before custody/succession can be promoted.
------------------------------------------------------------------------

record CurrentEntityEventTimeCustodyFrontier : Set where
  constructor current-entity-event-time-custody-frontier
  field
    entityContinuityThrough2021Paid : Bool
    postDeathEntitySurfaceRetained : Bool
    personInstitutionalContinuityThrough2019Paid : Bool
    exactEventTimeTechnicalRolePaid : Bool
    exactInstituteDerivativeIdentityPaid : Bool
    physicalCustodyPaid : Bool
    digitalCustodyPaid : Bool
    sameCarrierSuccessionPaid : Bool
    deathCausationPaid : Bool

open CurrentEntityEventTimeCustodyFrontier public

currentEntityEventTimeCustodyFrontier : CurrentEntityEventTimeCustodyFrontier
currentEntityEventTimeCustodyFrontier =
  current-entity-event-time-custody-frontier
    true true true false false false false false false

postDeathOfficersTarget : PostDeath.InstitutePostDeathReverseTarget
postDeathOfficersTarget = PostDeath.acquirePostDeathOfficers

annualReportsTarget : PostDeath.InstitutePostDeathReverseTarget
annualReportsTarget = PostDeath.acquireAnnualReports

postDeathTechnicalIPTarget : PostDeath.InstitutePostDeathReverseTarget
postDeathTechnicalIPTarget = PostDeath.acquireTechnicalIPSchedule

postDeathApparatusTarget : PostDeath.InstitutePostDeathReverseTarget
postDeathApparatusTarget = PostDeath.acquireApparatusCustody

postDeathNotebookRepositoryTarget : PostDeath.InstitutePostDeathReverseTarget
postDeathNotebookRepositoryTarget = PostDeath.acquireNotebookRepositoryCustody

postDeathResearchActivityTarget : PostDeath.InstitutePostDeathReverseTarget
postDeathResearchActivityTarget = PostDeath.acquirePostDeathResearchActivity
