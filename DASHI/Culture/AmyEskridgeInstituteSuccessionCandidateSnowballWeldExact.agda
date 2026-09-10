module DASHI.Culture.AmyEskridgeInstituteSuccessionCandidateSnowballWeldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Culture.AmyEskridgeInstituteTeamSuccessionSurfaceExact as Team
import DASHI.Culture.AmyEskridgeInstituteEntityContinuityExact as Entity
import DASHI.Culture.AmyEskridgeInstitutePostDeathContinuityExact as PostDeath
import DASHI.Culture.AmyEskridgePOAMSBoundaryCandidateExact as Candidate
import DASHI.Culture.AmyEskridgeApplicationTransformationExact as App
import DASHI.Culture.AmyEskridgeHoloChronPostDeathDissolutionFrontierExact as Holo
import DASHI.Culture.MissingDeceasedFullApplicationAcquisitionExact as Acquisition
import DASHI.Culture.MissingDeceasedReconstructionCostMatrixExact as Reconstruction
import DASHI.Culture.MissingDeceasedCustodyEventTimeMatrixExact as EventMatrix
import DASHI.Core.CapabilityReconstructionCostBidiExact as ReconstructionCore

------------------------------------------------------------------------
-- AMY ESKRIDGE MEMORIAL: INSTITUTE SUCCESSION-CANDIDATE SNOWBALL WELD
--
-- Existing owners already provide the team, entity-continuity, post-death
-- corporate-continuity, application-acquisition, reconstruction-cost, and
-- comparative event-time/custody coordinates. This adapter composes them;
-- it does not introduce another succession status model.
------------------------------------------------------------------------

poamsExactIdentityStillUnpaid :
  Candidate.poamsExactSameObjectEstablished Candidate.canonicalCurrentPOAMSCandidateAssessment ≡ false
poamsExactIdentityStillUnpaid = refl

amySuccessorStillUnrecovered :
  App.successorOrHandoverRecovered App.canonicalAmyApplicationTransformationFrontier ≡ false
amySuccessorStillUnrecovered = refl

amyApplicationAcquisitionRemainsHighestPriority :
  Acquisition.priority Acquisition.amyEskridgeAcquisition ≡ Acquisition.priorityHighest
amyApplicationAcquisitionRemainsHighestPriority = refl

instituteReconstructionCostStillUnknown :
  ReconstructionCore.costClass Reconstruction.eskridgeInstituteContinuity ≡ ReconstructionCore.unknown
instituteReconstructionCostStillUnknown = refl

------------------------------------------------------------------------
-- Existing continuity receipts that ARE paid.
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

instituteEntityContinuityDoesNotPayTechnicalAssetCustody :
  Entity.technicalAssetCustodyEstablished Entity.instituteEntityContinuity ≡ false
instituteEntityContinuityDoesNotPayTechnicalAssetCustody = refl

institutePostDeathEntitySurvivalDoesNotPayCarrierSurvival :
  PostDeath.entitySurvivalImpliesTechnicalCarrierSurvival
    PostDeath.canonicalInstituteContinuityBoundary ≡ false
institutePostDeathEntitySurvivalDoesNotPayCarrierSurvival = refl

instituteCorporateContinuityDoesNotPayPostDeathAssetTransfer :
  PostDeath.corporateContinuityImpliesPostDeathAssetTransfer
    PostDeath.canonicalInstituteContinuityBoundary ≡ false
instituteCorporateContinuityDoesNotPayPostDeathAssetTransfer = refl

------------------------------------------------------------------------
-- Project onto the existing comparative custody/event-time matrix.
-- Organisational continuity is already partial; custody and same-carrier
-- succession remain not-located rather than absent.
------------------------------------------------------------------------

amyEventTimeRoleIsPartial :
  EventMatrix.eventTimeRole EventMatrix.eskridgeRow ≡ EventMatrix.partial
amyEventTimeRoleIsPartial = refl

amyOrganisationalContinuityIsPartial :
  EventMatrix.organisationalContinuity EventMatrix.eskridgeRow ≡ EventMatrix.partial
amyOrganisationalContinuityIsPartial = refl

amyPhysicalCustodyStillNotLocated :
  EventMatrix.physicalCustody EventMatrix.eskridgeRow ≡ EventMatrix.notLocated
amyPhysicalCustodyStillNotLocated = refl

amyDigitalDataCustodyStillNotLocated :
  EventMatrix.digitalOrDataCustody EventMatrix.eskridgeRow ≡ EventMatrix.notLocated
amyDigitalDataCustodyStillNotLocated = refl

amySameCarrierSuccessionStillNotLocated :
  EventMatrix.sameCarrierSuccession EventMatrix.eskridgeRow ≡ EventMatrix.notLocated
amySameCarrierSuccessionStillNotLocated = refl

organisationalContinuityStillDoesNotPaySameCarrierTransfer :
  EventMatrix.organisationalContinuityImpliesSameCarrierTransfer
    EventMatrix.canonicalMatrixBoundary ≡ false
organisationalContinuityStillDoesNotPaySameCarrierTransfer = refl

notLocatedStillDoesNotMeanAbsent :
  EventMatrix.notLocatedImpliesAbsent EventMatrix.canonicalMatrixBoundary ≡ false
notLocatedStillDoesNotMeanAbsent = refl

------------------------------------------------------------------------
-- Historical team remains a candidate/witness surface, not carrier custody.
------------------------------------------------------------------------

amy2018TeamDoesNotPaySameExperimentPossession :
  Team.sameExperimentPossessionOwned Team.amyTeam ≡ false
amy2018TeamDoesNotPaySameExperimentPossession = refl

shantel2018TeamDoesNotPaySameExperimentPossession :
  Team.sameExperimentPossessionOwned Team.shantelButlerTeam ≡ false
shantel2018TeamDoesNotPaySameExperimentPossession = refl

nate2018TeamDoesNotPaySameExperimentPossession :
  Team.sameExperimentPossessionOwned Team.nateKloseTeam ≡ false
nate2018TeamDoesNotPaySameExperimentPossession = refl

sam2018TeamDoesNotPaySameExperimentPossession :
  Team.sameExperimentPossessionOwned Team.samReidTeam ≡ false
sam2018TeamDoesNotPaySameExperimentPossession = refl

paul2018TeamDoesNotPaySameExperimentPossession :
  Team.sameExperimentPossessionOwned Team.paulHandyTeam ≡ false
paul2018TeamDoesNotPaySameExperimentPossession = refl

richard2018TeamDoesNotPaySameExperimentPossession :
  Team.sameExperimentPossessionOwned Team.richardEskridgeTeam ≡ false
richard2018TeamDoesNotPaySameExperimentPossession = refl

------------------------------------------------------------------------
-- HoloChron post-death branch remains an acquisition frontier.
------------------------------------------------------------------------

holochronPrimaryDissolutionFilingStillUnlocated :
  Holo.primaryDissolutionFilingLocated Holo.holoChronReportedDissolution ≡ false
holochronPrimaryDissolutionFilingStillUnlocated = refl

holochronTechnicalAssetDispositionStillUnlocated :
  Holo.technicalAssetDispositionLocated Holo.holoChronReportedDissolution ≡ false
holochronTechnicalAssetDispositionStillUnlocated = refl

------------------------------------------------------------------------
-- Existing reverse targets, ordered after the already-paid entity layer.
------------------------------------------------------------------------

roleContinuityTarget : Team.EskridgeTeamReverseTarget
roleContinuityTarget = Team.acquire2018To2020RoleContinuity

experimentAssignmentTarget : Team.EskridgeTeamReverseTarget
experimentAssignmentTarget = Team.acquireExperimentAssignment

instituteDerivativeIdentityTarget : Team.EskridgeTeamReverseTarget
instituteDerivativeIdentityTarget = Team.acquireInstituteDerivativeIdentity

notebookRepositoryCustodyTarget : Team.EskridgeTeamReverseTarget
notebookRepositoryCustodyTarget = Team.acquireNotebookOrRepositoryCustody

apparatusCustodyTarget : Team.EskridgeTeamReverseTarget
apparatusCustodyTarget = Team.acquireApparatusCustody

calibrationDataCustodyTarget : Team.EskridgeTeamReverseTarget
calibrationDataCustodyTarget = Team.acquireCalibrationDataCustody

postDeathHandoverArchiveTarget : Team.EskridgeTeamReverseTarget
postDeathHandoverArchiveTarget = Team.acquirePostDeathHandoverOrArchive

postDeathOfficersTarget : PostDeath.InstitutePostDeathReverseTarget
postDeathOfficersTarget = PostDeath.acquirePostDeathOfficers

postDeathResearchActivityTarget : PostDeath.InstitutePostDeathReverseTarget
postDeathResearchActivityTarget = PostDeath.acquirePostDeathResearchActivity

record InstituteSuccessionCandidateBoundary : Set where
  constructor institute-succession-candidate-boundary
  field
    historicalTeamMaySeedSuccessionSearch : Bool
    historicalTeamAutomaticallyIdentifiesSuccessor : Bool
    historicalTeamAutomaticallyPaysSameExperimentPossession : Bool
    multiYearEntityContinuityIsOwned : Bool
    entityContinuityAutomaticallyPaysPersonRoleContinuity : Bool
    entityContinuityAutomaticallyPaysTechnicalCarrierContinuity : Bool
    postDeathEntitySurfaceIsOwned : Bool
    postDeathEntitySurfaceAutomaticallyPaysAssetTransfer : Bool
    organisationalContinuityIsAlreadyPartial : Bool
    partialOrganisationalContinuityAutomaticallyPaysSameCarrierTransfer : Bool
    overlappingTeamAutomaticallyPaysLowReconstructionCost : Bool
    overlappingTeamAutomaticallyPaysSameCarrierTransfer : Bool
    postDeathDissolutionAutomaticallyPaysAssetDisposition : Bool
    exactDerivativeIdentityStillPrecedesSameCarrierSuccession : Bool
    successionEvidenceMayBeRetainedBeforeIdentityCloses : Bool
    successionOrCustodyCreatesDeathCausation : Bool

open InstituteSuccessionCandidateBoundary public

canonicalInstituteSuccessionCandidateBoundary : InstituteSuccessionCandidateBoundary
canonicalInstituteSuccessionCandidateBoundary =
  institute-succession-candidate-boundary
    true false false
    true false false
    true false
    true false
    false false false
    true true false

------------------------------------------------------------------------
-- Current composed interpretation:
--
--  * Institute entity continuity through 2019-2021 is source-backed;
--  * a post-death Institute corporate-survival surface is retained;
--  * the authoritative comparative matrix already upgrades organisational
--    continuity from wholly-open to PARTIAL;
--  * physical custody, digital/data custody and same-carrier succession remain
--    NOT LOCATED, which is not the same proposition as absent;
--  * exact Institute derivative identity remains the first application leaf;
--  * after identity, retained team/entity surfaces can be queried directly for
--    person-level role continuity, experiment assignment, custody and handover.
------------------------------------------------------------------------
