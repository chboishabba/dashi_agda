module DASHI.Culture.AmyEskridgeInstituteTeamSuccessionSurfaceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- INSTITUTE TEAM / SUCCESSION SURFACE
--
-- Amy Eskridge's official HAL5 presentation deck (Dec 2018) identifies a
-- multi-person Institute/HoloChron team.  This provides concrete witness and
-- succession candidates for later application-transformation acquisition.
-- It does not establish that each listed person worked on the same experiment,
-- possessed the same data, or remained involved through 2020-2022.
------------------------------------------------------------------------

data InstituteRole : Set where
  president
  researchDirector
  creativeDirector
  governmentAffairsDirector
  seniorElectricalEngineer
  professorEmeritus
  holoChronCTO
  : InstituteRole

record TeamMemberReceipt : Set where
  constructor team-member-receipt
  field
    person : String
    role : InstituteRole
    sourceReference : String
    sameExperimentPossessionOwned : Bool
    sameExperimentPossessionOwnedIsFalse : sameExperimentPossessionOwned ≡ false

open TeamMemberReceipt public

amyTeam : TeamMemberReceipt
amyTeam = team-member-receipt "Amy Eskridge" president "HAL5 Dec 2018 presentation, team slide" false refl

shantelButlerTeam : TeamMemberReceipt
shantelButlerTeam = team-member-receipt "Shantel Butler" researchDirector "HAL5 Dec 2018 presentation, team slide" false refl

nateKloseTeam : TeamMemberReceipt
nateKloseTeam = team-member-receipt "Nate Klose" creativeDirector "HAL5 Dec 2018 presentation, team slide" false refl

samReidTeam : TeamMemberReceipt
samReidTeam = team-member-receipt "Sam Reid" governmentAffairsDirector "HAL5 Dec 2018 presentation, team slide" false refl

paulHandyTeam : TeamMemberReceipt
paulHandyTeam = team-member-receipt "Paul Handy" seniorElectricalEngineer "HAL5 Dec 2018 presentation, team slide" false refl

richardEskridgeTeam : TeamMemberReceipt
richardEskridgeTeam = team-member-receipt "Richard Eskridge" holoChronCTO "HAL5 Dec 2018 presentation, team + HoloChron slides" false refl

record InstituteTeamBoundary : Set where
  constructor institute-team-boundary
  field
    listedTeamImpliesSharedExperimentalCarrier : Bool
    listedTeamImpliesSharedExperimentalCarrierIsFalse :
      listedTeamImpliesSharedExperimentalCarrier ≡ false
    listedRoleSupportsWitnessAcquisition : Bool
    listedRoleSupportsWitnessAcquisitionIsTrue :
      listedRoleSupportsWitnessAcquisition ≡ true
    laterContinuityRequiresIndependentReceipt : Bool
    laterContinuityRequiresIndependentReceiptIsTrue :
      laterContinuityRequiresIndependentReceipt ≡ true

canonicalInstituteTeamBoundary : InstituteTeamBoundary
canonicalInstituteTeamBoundary = institute-team-boundary false refl true refl true refl

data EskridgeTeamReverseTarget : Set where
  acquire2018To2020RoleContinuity
  acquireExperimentAssignment
  acquireNotebookOrRepositoryCustody
  acquireApparatusCustody
  acquireCalibrationDataCustody
  acquireInstituteDerivativeIdentity
  acquirePostDeathHandoverOrArchive
  : EskridgeTeamReverseTarget
