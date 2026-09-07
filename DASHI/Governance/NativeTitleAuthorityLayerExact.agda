module DASHI.Governance.NativeTitleAuthorityLayerExact where

open import DASHI.Core.Prelude
import DASHI.Governance.IndigenousEnvironmentalJusticeSourceRegistryExact as Sources

------------------------------------------------------------------------
-- NATIVE TITLE: COMMUNITY / RIGHTS-HOLDER / LEGAL-CORPORATE ROLE SEPARATION
--
-- Native Title Act 1993 (Cth), especially s223 and ss55-57.
-- ORIC, Native title and RNTBCs.
--
-- The legal apparatus is represented honestly without promoting statutory or
-- common-law recognition into identity with community sovereignty/authority.
------------------------------------------------------------------------

data AuthorityRole : Set where
  traditionalOwnerCommunity : AuthorityRole
  commonLawHolder : AuthorityRole
  claimApplicant : AuthorityRole
  prescribedBodyCorporate : AuthorityRole
  registeredNativeTitleBodyCorporate : AuthorityRole


data RoleFunction : Set where
  holdsTraditionalLawCustom : RoleFunction
  holdsRecognizedNativeTitleInterest : RoleFunction
  conductsClaimProcedure : RoleFunction
  holdsOrManagesRecognizedRights : RoleFunction
  representsInterestsUnderStatute : RoleFunction


data Performs : AuthorityRole → RoleFunction → Set where
  communityLawCustom : Performs traditionalOwnerCommunity holdsTraditionalLawCustom
  holderInterest : Performs commonLawHolder holdsRecognizedNativeTitleInterest
  applicantClaim : Performs claimApplicant conductsClaimProcedure
  pbcManage : Performs prescribedBodyCorporate holdsOrManagesRecognizedRights
  rntbcManage : Performs registeredNativeTitleBodyCorporate holdsOrManagesRecognizedRights
  rntbcRepresents : Performs registeredNativeTitleBodyCorporate representsInterestsUnderStatute

communityIsNotRntbc : traditionalOwnerCommunity ≡ registeredNativeTitleBodyCorporate → ⊥
communityIsNotRntbc ()

commonLawHolderIsNotRntbc : commonLawHolder ≡ registeredNativeTitleBodyCorporate → ⊥
commonLawHolderIsNotRntbc ()

claimApplicantIsNotRntbc : claimApplicant ≡ registeredNativeTitleBodyCorporate → ⊥
claimApplicantIsNotRntbc ()

nativeTitleActSource : Sources.SourceReference
nativeTitleActSource = Sources.nativeTitleAct1993

oricSource : Sources.SourceReference
oricSource = Sources.oricRntbc

record NativeTitleAuthorityBoundary : Set where
  constructor nativeTitleAuthorityBoundary
  field
    traditionalOwnerCommunityEqualsRntbc : Bool
    traditionalOwnerCommunityEqualsRntbcIsFalse : traditionalOwnerCommunityEqualsRntbc ≡ false
    commonLawHolderEqualsManagingCorporation : Bool
    commonLawHolderEqualsManagingCorporationIsFalse : commonLawHolderEqualsManagingCorporation ≡ false
    claimApplicantEqualsPostDeterminationManager : Bool
    claimApplicantEqualsPostDeterminationManagerIsFalse : claimApplicantEqualsPostDeterminationManager ≡ false
    legalRecognitionExhaustsCommunityAuthority : Bool
    legalRecognitionExhaustsCommunityAuthorityIsFalse : legalRecognitionExhaustsCommunityAuthority ≡ false
    statutoryRepresentationEqualsSovereignty : Bool
    statutoryRepresentationEqualsSovereigntyIsFalse : statutoryRepresentationEqualsSovereignty ≡ false

canonicalNativeTitleAuthorityBoundary : NativeTitleAuthorityBoundary
canonicalNativeTitleAuthorityBoundary =
  nativeTitleAuthorityBoundary false refl false refl false refl false refl false refl
