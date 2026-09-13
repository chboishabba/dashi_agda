module DASHI.Culture.AmyEskridgeInstituteTeamSECContinuitySnowballWeldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Core.PersonIdentityAttributionBidiExact as Identity
import DASHI.Culture.MissingDeceasedIdentityAttributionAuditExact as IdentityAudit
import DASHI.Culture.AmyEskridgeInstituteTeamSuccessionSurfaceExact as Team
import DASHI.Culture.AmyEskridgeCorporateCustodySurfaceExact as Corporate
import DASHI.Culture.AmyEskridgeCorporateInstitutionalChronologySnowballExact as Chron
import DASHI.Culture.AmyEskridgeInstituteSuccessionCandidateSnowballWeldExact as Succession

------------------------------------------------------------------------
-- AMY ESKRIDGE MEMORIAL: 2018 TEAM / 2019 SEC CONTINUITY SNOWBALL WELD
--
-- The existing 2018 HAL5 team carrier and the issuer-filed 2019 SEC Form D
-- are composed at the person surface.  Shantel pays a literal displayed-name
-- overlap.  Amy's HAL5/public-name surface and the SEC married/legal-name form
-- are joined only through the pre-existing source-backed identity audit.
--
-- Nate/Nathan Klose and Sam/Samuel Reid are deliberately not promoted here:
-- their cross-carrier use still requires an explicit identity/name-normalisation
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

------------------------------------------------------------------------
-- AMY 2018 -> 2019 ROLE CONTINUITY VIA EXISTING IDENTITY AUDIT
------------------------------------------------------------------------

amyIdentityReceipt : Identity.IdentityReceipt
amyIdentityReceipt = IdentityAudit.amyEskridgeIdentity

amyIdentityIsSourceBacked :
  Identity.status IdentityAudit.amyEskridgeIdentity ≡ Identity.identitySourceBacked
amyIdentityIsSourceBacked = refl

amy2018DisplayedNameExact :
  Team.person Team.amyTeam ≡ "Amy Eskridge"
amy2018DisplayedNameExact = refl

amy2018RoleIsPresident :
  Team.role Team.amyTeam ≡ Team.president
amy2018RoleIsPresident = refl

amy2019InstitutePresidentOwned :
  Corporate.amyPresident Corporate.instituteCorporateSurface ≡ true
amy2019InstitutePresidentOwned = refl

record Amy2018To2019InstitutionalContinuityFrontier : Set where
  constructor amy-2018-to-2019-institutional-continuity-frontier
  field
    identityAliasWeldPaid : Bool
    hal5InstituteRolePaid : Bool
    secInstituteRolePaid : Bool
    personInstitutionalContinuity2018To2019Paid : Bool
    sameExperimentContinuityPaid : Bool
    technicalCustodyContinuityPaid : Bool
    applicationCarrierContinuityPaid : Bool

open Amy2018To2019InstitutionalContinuityFrontier public

amy2018To2019InstitutionalContinuityFrontier : Amy2018To2019InstitutionalContinuityFrontier
amy2018To2019InstitutionalContinuityFrontier =
  amy-2018-to-2019-institutional-continuity-frontier
    true true true true false false false

------------------------------------------------------------------------
-- 2020 Amy role-continuity acquisition cut.
--
-- A concrete Alabama Secretary of State 2020 annual-report locator is retained
-- by the institutional chronology.  It remains primaryRecordIdentified rather
-- than exactPrimaryCarrierInspected, so the 2018-to-2020 role-continuity target
-- is not silently paid by the now-closed 2018-to-2019 person-role weld.
------------------------------------------------------------------------

amy2020AnnualReportPrimaryCarrierIdentified :
  Chron.entitlement Chron.institute2020AmyPresidentAnnualReportLeadAtom ≡
    Chron.primaryRecordIdentified
amy2020AnnualReportPrimaryCarrierIdentified = refl

record Amy2020RoleContinuityAcquisitionFrontier : Set where
  constructor amy-2020-role-continuity-acquisition-frontier
  field
    amy2018TeamCarrierPaid : Bool
    amy2018To2019InstitutionalContinuityPaid : Bool
    official2020AnnualReportLocatorIdentified : Bool
    exact2020PrimaryCarrierInspected : Bool
    institutionalRoleContinuityThrough2020Paid : Bool
    sameExperimentContinuityThrough2020Paid : Bool
    technicalCustodyThrough2020Paid : Bool

open Amy2020RoleContinuityAcquisitionFrontier public

amy2020RoleContinuityAcquisitionFrontier : Amy2020RoleContinuityAcquisitionFrontier
amy2020RoleContinuityAcquisitionFrontier =
  amy-2020-role-continuity-acquisition-frontier
    true true true false false false false

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
    sourceBackedIdentityMayPayPersonRoleAttribution : Bool
    exactNameOverlapAutomaticallyPaysSameExperiment : Bool
    sourceBackedPersonIdentityAutomaticallyPaysSameExperiment : Bool
    directorOrPresidentRoleAutomaticallyPaysTechnicalCustody : Bool
    2018To2019ContinuityAutomaticallyPays2018To2020Continuity : Bool
    personContinuityAutomaticallyPaysPostDeathSuccession : Bool
    nateNathanAliasPaidWithoutReceipt : Bool
    samSamuelAliasPaidWithoutReceipt : Bool
    institutionalContinuityCreatesDeathCausation : Bool

open TeamSECContinuityBoundary public

canonicalTeamSECContinuityBoundary : TeamSECContinuityBoundary
canonicalTeamSECContinuityBoundary =
  team-sec-continuity-boundary
    true true false false false false false false false false
