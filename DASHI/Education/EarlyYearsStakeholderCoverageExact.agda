module DASHI.Education.EarlyYearsStakeholderCoverageExact where

open import DASHI.Core.Prelude
import DASHI.Core.ActiveObligationEvidenceFibreExact as Active
import DASHI.Core.RequiredAxisSupportSquareExact as Required
import DASHI.Core.RequiredObserverAxisJoinAdequacyExact as Join

------------------------------------------------------------------------
-- STAKEHOLDER-INDEXED CLAIM COVERAGE
--
-- The key boundary is not "missing stakeholder => invalid project".  A claim
-- declares the stakeholder observation axes it actually requires.  Missing an
-- inactive axis is harmless; missing an active axis blocks discharge of that
-- claim.  This specializes the #582 active-obligation and required-axis cores
-- rather than introducing a parallel qualitative-research logic.
------------------------------------------------------------------------

data StakeholderAxis : Set where
  professionalAxis familyAxis childAxis communityAxis : StakeholderAxis

data EvidenceStage : Set where
  professionalPilot familyJoined childJoined communityJoined : EvidenceStage

data EarlyYearsClaim : Set where
  professionalPracticeClaim familyExperienceClaim childExperienceClaim communityExperienceClaim : EarlyYearsClaim

data Never : Set where

ClaimRequires : EvidenceStage → EarlyYearsClaim → StakeholderAxis → Set
ClaimRequires _ professionalPracticeClaim professionalAxis = ⊤
ClaimRequires _ familyExperienceClaim professionalAxis = ⊤
ClaimRequires _ familyExperienceClaim familyAxis = ⊤
ClaimRequires _ childExperienceClaim professionalAxis = ⊤
ClaimRequires _ childExperienceClaim familyAxis = ⊤
ClaimRequires _ childExperienceClaim childAxis = ⊤
ClaimRequires _ communityExperienceClaim professionalAxis = ⊤
ClaimRequires _ communityExperienceClaim communityAxis = ⊤
ClaimRequires _ _ _ = Never

positive : Required.SupportSquare
positive = Required.supportSquare true false

missing : Required.SupportSquare
missing = Required.supportSquare false false

EvidenceAt : EvidenceStage → EarlyYearsClaim → StakeholderAxis → Required.SupportSquare
EvidenceAt professionalPilot _ professionalAxis = positive
EvidenceAt familyJoined _ professionalAxis = positive
EvidenceAt familyJoined _ familyAxis = positive
EvidenceAt childJoined _ professionalAxis = positive
EvidenceAt childJoined _ familyAxis = positive
EvidenceAt childJoined _ childAxis = positive
EvidenceAt communityJoined _ professionalAxis = positive
EvidenceAt communityJoined _ communityAxis = positive
EvidenceAt _ _ _ = missing

stakeholderObligations :
  Active.ActiveObligationFamily EvidenceStage EarlyYearsClaim StakeholderAxis
stakeholderObligations = Active.activeObligationFamily ClaimRequires EvidenceAt

------------------------------------------------------------------------
-- The current professional pilot can discharge a bounded professional-practice
-- claim.  No family/child/community evidence is required for that claim.
------------------------------------------------------------------------

professionalPilotResolvesProfessionalPractice :
  Active.ResolvedFor stakeholderObligations professionalPilot professionalPracticeClaim
professionalPilotResolvesProfessionalPractice professionalAxis tt = refl , refl
professionalPilotResolvesProfessionalPractice familyAxis ()
professionalPilotResolvesProfessionalPractice childAxis ()
professionalPilotResolvesProfessionalPractice communityAxis ()

------------------------------------------------------------------------
-- The same evidence stage cannot discharge a family-experience claim because
-- family observation is active for that claim and missing at this stage.
------------------------------------------------------------------------

missingFamilyAtProfessionalPilot :
  Active.MissingActiveObligation
    stakeholderObligations professionalPilot familyExperienceClaim
missingFamilyAtProfessionalPilot =
  Active.missingActiveObligation familyAxis tt (refl , refl)

professionalPilotCannotEstablishFamilyExperience :
  Active.ResolvedFor stakeholderObligations professionalPilot familyExperienceClaim → ⊥
professionalPilotCannotEstablishFamilyExperience =
  Active.missingActiveObligationBlocksResolution missingFamilyAtProfessionalPilot

familyJoinedResolvesFamilyExperience :
  Active.ResolvedFor stakeholderObligations familyJoined familyExperienceClaim
familyJoinedResolvesFamilyExperience professionalAxis tt = refl , refl
familyJoinedResolvesFamilyExperience familyAxis tt = refl , refl
familyJoinedResolvesFamilyExperience childAxis ()
familyJoinedResolvesFamilyExperience communityAxis ()

missingChildAtFamilyJoined :
  Active.MissingActiveObligation
    stakeholderObligations familyJoined childExperienceClaim
missingChildAtFamilyJoined =
  Active.missingActiveObligation childAxis tt (refl , refl)

familyEvidenceStillCannotEstablishChildExperience :
  Active.ResolvedFor stakeholderObligations familyJoined childExperienceClaim → ⊥
familyEvidenceStillCannotEstablishChildExperience =
  Active.missingActiveObligationBlocksResolution missingChildAtFamilyJoined

childJoinedResolvesChildExperience :
  Active.ResolvedFor stakeholderObligations childJoined childExperienceClaim
childJoinedResolvesChildExperience professionalAxis tt = refl , refl
childJoinedResolvesChildExperience familyAxis tt = refl , refl
childJoinedResolvesChildExperience childAxis tt = refl , refl
childJoinedResolvesChildExperience communityAxis ()

------------------------------------------------------------------------
-- Observer-axis reading.  When a claim requires both professional and family
-- coordinates, carrying both constructs their joint factorisation.  Strength
-- on one axis cannot compensate for failure to retain the other.
------------------------------------------------------------------------

jointRequiredAxisLaw = Join.candidateRetainingBothRetainsJoint
missingRequiredLeftAxisBlocksJointClaim = Join.leftAxisDefectBlocksRetainingBoth
missingRequiredRightAxisBlocksJointClaim = Join.rightAxisDefectBlocksRetainingBoth

record StakeholderCoverageBoundary : Set where
  constructor stakeholderCoverageBoundary
  field
    claimRequirementsAreStakeholderIndexed : Bool
    missingInactiveStakeholderInvalidatesClaim : Bool
    missingActiveStakeholderBlocksDirectClaim : Bool
    professionalEvidenceAloneEstablishesFamilyExperience : Bool
    familyEvidenceAloneEstablishesChildExperience : Bool
    addingRequiredStakeholderCanCloseObligation : Bool
    jointCoverageMeansWorldCompleteness : Bool

canonicalStakeholderCoverageBoundary : StakeholderCoverageBoundary
canonicalStakeholderCoverageBoundary =
  stakeholderCoverageBoundary true false true false false true false
