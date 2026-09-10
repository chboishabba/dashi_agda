module DASHI.Culture.AmyEskridgeInstituteSuccessionCandidateSnowballWeldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Culture.AmyEskridgeInstituteTeamSuccessionSurfaceExact as Team
import DASHI.Culture.AmyEskridgePOAMSBoundaryCandidateExact as Candidate
import DASHI.Culture.AmyEskridgeApplicationTransformationExact as App
import DASHI.Culture.AmyEskridgeHoloChronPostDeathDissolutionFrontierExact as Holo
import DASHI.Culture.MissingDeceasedFullApplicationAcquisitionExact as Acquisition
import DASHI.Culture.MissingDeceasedReconstructionCostMatrixExact as Reconstruction
import DASHI.Core.CapabilityReconstructionCostBidiExact as ReconstructionCore

------------------------------------------------------------------------
-- AMY ESKRIDGE MEMORIAL: INSTITUTE SUCCESSION-CANDIDATE SNOWBALL WELD
--
-- The repo already identifies a multi-person Institute/HoloChron team, a
-- highest-priority Amy application-acquisition target, and an unknown
-- reconstruction-cost profile with an overlapping-team receipt.  This adapter
-- composes those owners without upgrading historical team membership into
-- exact 2020-2022 same-experiment possession, successor identity, custody, or
-- post-death transfer.
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

holochronPrimaryDissolutionFilingStillUnlocated :
  Holo.primaryDissolutionFilingLocated Holo.holoChronReportedDissolution ≡ false
holochronPrimaryDissolutionFilingStillUnlocated = refl

holochronTechnicalAssetDispositionStillUnlocated :
  Holo.technicalAssetDispositionLocated Holo.holoChronReportedDissolution ≡ false
holochronTechnicalAssetDispositionStillUnlocated = refl

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

record InstituteSuccessionCandidateBoundary : Set where
  constructor institute-succession-candidate-boundary
  field
    historicalTeamMaySeedSuccessionSearch : Bool
    historicalTeamAutomaticallyIdentifiesSuccessor : Bool
    historicalTeamAutomaticallyPaysSameExperimentPossession : Bool
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
    true false false false false false true true false

------------------------------------------------------------------------
-- Current composed interpretation:
--
--  * 2018 team identities are concrete succession/witness candidates;
--  * overlapping-team continuity is retained;
--  * no listed member is yet a same-experiment or same-carrier successor;
--  * exact Institute derivative identity remains the first application leaf;
--  * once that object is identified, the same existing candidate set can be
--    queried for role continuity, custody, and handover rather than rediscovered.
------------------------------------------------------------------------
