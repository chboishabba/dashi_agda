module DASHI.Culture.AmyEskridgeEntityEventTimeCustodySnowballWeldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Culture.AmyEskridgeInstituteEntityContinuityExact as Entity
import DASHI.Culture.AmyEskridgeInstitutePostDeathContinuityExact as PostDeath
import DASHI.Culture.MissingDeceasedCustodyEventTimeMatrixExact as Matrix
import DASHI.Culture.AmyEskridgeInstituteTeamSECContinuitySnowballWeldExact as Role
import DASHI.Culture.AmyEskridgePOAMSApplicationCustodySnowballWeldExact as POAMS
import DASHI.Culture.AmyEskridgeApplicationTransformationExact as App

------------------------------------------------------------------------
-- AMY ESKRIDGE MEMORIAL: ENTITY / EVENT-TIME / CUSTODY SNOWBALL WELD
--
-- Existing owners already establish a multi-year Institute entity surface and
-- a post-death corporate-entity surface. This adapter composes those receipts
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
-- Current composed reading.
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

------------------------------------------------------------------------
-- ORDERED PAYMENT / OUT-OF-ORDER ACQUISITION ROUTER
--
-- The repo may already contain later custody, archive or succession evidence.
-- Snowball acquisition permits retaining it immediately, but the application
-- consumer still pays the first unpaid dependency first. For the current Amy
-- application transformation that leaf is exact Institute derivative identity.
------------------------------------------------------------------------

firstApplicationCarrierLeafIsExactDerivativeIdentity :
  App.firstAmyApplicationMissingLeaf ≡ App.acquireInstituteDerivedObjectIdentity
firstApplicationCarrierLeafIsExactDerivativeIdentity = refl

firstApplicationCarrierTarget : App.AmyApplicationReverseTarget
firstApplicationCarrierTarget = App.acquireInstituteDerivedObjectIdentity

applicationApparatusTarget : App.AmyApplicationReverseTarget
applicationApparatusTarget = App.acquireApparatusGeometry

applicationDataTarget : App.AmyApplicationReverseTarget
applicationDataTarget = App.acquireRawAndReducedData

applicationNotebookWorkflowTarget : App.AmyApplicationReverseTarget
applicationNotebookWorkflowTarget = App.acquireLabNotebookOrVersionedWorkflow

applicationSuccessorTarget : App.AmyApplicationReverseTarget
applicationSuccessorTarget = App.acquireSuccessorOrHandover

record CurrentResidualRouter : Set where
  constructor current-residual-router
  field
    exactDerivativeIdentityIsFirstUnpaid : Bool
    laterApparatusEvidenceMayBeRetained : Bool
    laterDataEvidenceMayBeRetained : Bool
    laterNotebookRepositoryEvidenceMayBeRetained : Bool
    laterSuccessorEvidenceMayBeRetained : Bool
    laterCarrierEvidenceMaySkipExactIdentity : Bool
    entityContinuityMayManufactureExactIdentity : Bool
    postDeathEntitySurfaceMayManufactureExactIdentity : Bool
    retainedLaterEvidenceAutomaticallyPaysIdentity : Bool

open CurrentResidualRouter public

currentResidualRouter : CurrentResidualRouter
currentResidualRouter =
  current-residual-router
    true true true true true
    false false false false

------------------------------------------------------------------------
-- Post-death source targets remain retained in parallel. They can sharpen the
-- graph before exact application identity closes, but cannot silently leapfrog
-- the identity dependency for same-carrier custody/succession conclusions.
------------------------------------------------------------------------

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
