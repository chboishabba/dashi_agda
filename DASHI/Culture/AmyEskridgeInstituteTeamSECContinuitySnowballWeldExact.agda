module DASHI.Culture.AmyEskridgeInstituteTeamSECContinuitySnowballWeldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Culture.AmyEskridgeInstituteTeamSuccessionSurfaceExact as Team
import DASHI.Culture.AmyEskridgeCorporateCustodySurfaceExact as Corporate
import DASHI.Culture.AmyEskridgeCorporateInstitutionalChronologySnowballExact as Chron
import DASHI.Culture.AmyEskridgeInstituteSuccessionCandidateSnowballWeldExact as Succession

------------------------------------------------------------------------
-- AMY ESKRIDGE MEMORIAL: 2018 TEAM / 2019 SEC CONTINUITY SNOWBALL WELD
--
-- The existing 2018 HAL5 team carrier and the issuer-filed 2019 SEC Form D
-- had not yet been composed at the person surface.  This adapter pays only the
-- narrow exact-name overlap that does not require an alias normalisation:
-- Shantel Butler is listed on the 2018 Institute team and is independently
-- represented by the structured 2019 corporate owner as an Institute director.
--
-- Nate/Nathan Klose and Sam/Samuel Reid are deliberately not promoted here:
-- their cross-carrier use requires an explicit identity/name-normalisation
-- receipt rather than silent string aliasing.
------------------------------------------------------------------------

shantel2018TeamReceipt : Team.TeamMemberReceipt
shantel2018TeamReceipt = Team.shantelButlerTeam

shantel2018DisplayedNameExact :
  Team.person Team.shantelButlerTeam ≡ "Shantel Butler"
shantel2018DisplayedNameExact = refl

shantel2018RoleIsResearchDirector :
  Team.role Team.shantelButlerTeam ≡ Team.researchDirector
shantel2018RoleIsResearchDirector = refl

secOfficerCarrierIsExactPrimary :
  Chron.entitlement Chron.secAmyOfficerDirectorAtom ≡ Chron.exactPrimaryCarrierInspected
secOfficerCarrierIsExactPrimary = refl

shantel2019InstituteDirectorOwned :
  Corporate.shantelButlerDirector Corporate.instituteCorporateSurface ≡ true
shantel2019InstituteDirectorOwned = refl

------------------------------------------------------------------------
-- What this composition pays:
--
--   2018: Shantel Butler is a named Institute/HoloChron team member.
--   2019: an issuer-filed SEC carrier independently places Shantel Butler on
--         the Institute corporate surface as a director.
--
-- This is a person-level institutional-continuity witness across two source
-- carriers.  It is not an experiment-assignment, apparatus, notebook,
-- repository, calibration-data, IP, or post-death handover receipt.
------------------------------------------------------------------------

record TeamSECContinuityFrontier : Set where
  constructor team-sec-continuity-frontier
  field
    exactName2018To2019OverlapPaid : Bool
    independent2019PrimaryCarrierPaid : Bool
    personInstitutionalContinuityCandidateAdvanced : Bool
    sameExperimentPossessionPaid : Bool
    technicalIPCustodyPaid : Bool
    apparatusCustodyPaid : Bool
    notebookRepositoryCustodyPaid : Bool
    calibrationDataCustodyPaid : Bool
    roleContinuityThrough2020Paid : Bool
    postDeathHandoverPaid : Bool
    deathCausationPaid : Bool

open TeamSECContinuityFrontier public

shantelTeamSECContinuityFrontier : TeamSECContinuityFrontier
shantelTeamSECContinuityFrontier =
  team-sec-continuity-frontier
    true true true
    false false false false false false false false

shantelSameExperimentStillUnpaid :
  Team.sameExperimentPossessionOwned Team.shantelButlerTeam ≡ false
shantelSameExperimentStillUnpaid = refl

successionStillDoesNotFollowFromOverlap :
  Succession.historicalTeamAutomaticallyIdentifiesSuccessor
    Succession.canonicalInstituteSuccessionCandidateBoundary ≡ false
successionStillDoesNotFollowFromOverlap = refl

sameCarrierTransferStillDoesNotFollowFromOverlap :
  Succession.overlappingTeamAutomaticallyPaysSameCarrierTransfer
    Succession.canonicalInstituteSuccessionCandidateBoundary ≡ false
sameCarrierTransferStillDoesNotFollowFromOverlap = refl

roleContinuityThrough2020Target : Team.EskridgeTeamReverseTarget
roleContinuityThrough2020Target = Team.acquire2018To2020RoleContinuity

experimentAssignmentTarget : Team.EskridgeTeamReverseTarget
experimentAssignmentTarget = Team.acquireExperimentAssignment

notebookRepositoryCustodyTarget : Team.EskridgeTeamReverseTarget
notebookRepositoryCustodyTarget = Team.acquireNotebookOrRepositoryCustody

apparatusCustodyTarget : Team.EskridgeTeamReverseTarget
apparatusCustodyTarget = Team.acquireApparatusCustody

calibrationDataCustodyTarget : Team.EskridgeTeamReverseTarget
calibrationDataCustodyTarget = Team.acquireCalibrationDataCustody

postDeathHandoverArchiveTarget : Team.EskridgeTeamReverseTarget
postDeathHandoverArchiveTarget = Team.acquirePostDeathHandoverOrArchive

record TeamSECContinuityBoundary : Set where
  constructor team-sec-continuity-boundary
  field
    exactNameOverlapMayAdvanceWitnessPriority : Bool
    exactNameOverlapAutomaticallyPaysSameExperiment : Bool
    directorRoleAutomaticallyPaysTechnicalCustody : Bool
    2018To2019ContinuityAutomaticallyPays2018To2020Continuity : Bool
    personContinuityAutomaticallyPaysPostDeathSuccession : Bool
    nateNathanAliasPaidWithoutReceipt : Bool
    samSamuelAliasPaidWithoutReceipt : Bool
    institutionalContinuityCreatesDeathCausation : Bool

open TeamSECContinuityBoundary public

canonicalTeamSECContinuityBoundary : TeamSECContinuityBoundary
canonicalTeamSECContinuityBoundary =
  team-sec-continuity-boundary true false false false false false false false
