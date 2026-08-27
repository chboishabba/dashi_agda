module DASHI.Governance.KunmingMontrealTarget3AuthorityBoundaryExact where

open import DASHI.Core.Prelude
import DASHI.Governance.EnvironmentalAuthoritySourceRegistryRound2Exact as Sources

------------------------------------------------------------------------
-- KUNMING-MONTREAL GLOBAL BIODIVERSITY FRAMEWORK TARGET 3
--
-- The adopted text requires 30% conservation by 2030 through equitably governed
-- protected/OECM systems, recognizes Indigenous and traditional territories,
-- and requires recognition/respect for Indigenous Peoples' and local
-- communities' rights including over traditional territories.  Section C also
-- requires respect for rights/knowledge/worldviews and FPIC safeguards.
------------------------------------------------------------------------

data ConservationCoverage : Set where
  belowThirty targetThirty : ConservationCoverage

data TerritorialAuthority : Set where
  externallyAdministered originatingCommunityAuthority : TerritorialAuthority

data RightsImplementation : Set where
  rightsTextOnly rightsRespectOperationalized : RightsImplementation

record Target3State : Set where
  constructor target3State
  field
    coverage : ConservationCoverage
    authority : TerritorialAuthority
    rightsImplementation : RightsImplementation

coverageWithoutAuthorityTransfer : Target3State
coverageWithoutAuthorityTransfer = target3State targetThirty externallyAdministered rightsTextOnly

thirtyPercentDoesNotConstructOriginatingAuthority :
  Target3State.authority coverageWithoutAuthorityTransfer ≡ originatingCommunityAuthority → ⊥
thirtyPercentDoesNotConstructOriginatingAuthority ()

rightsLanguageDoesNotDefinitionallyEqualImplementation :
  Target3State.rightsImplementation coverageWithoutAuthorityTransfer ≡ rightsRespectOperationalized → ⊥
rightsLanguageDoesNotDefinitionallyEqualImplementation ()

source : Sources.SourceReference
source = Sources.kunmingMontreal2022

record Target3Boundary : Set where
  constructor target3Boundary
  field
    conservationCoverageEqualsTerritorialAuthority : Bool
    conservationCoverageEqualsTerritorialAuthorityIsFalse : conservationCoverageEqualsTerritorialAuthority ≡ false
    frameworkRightsLanguageEqualsLocalImplementation : Bool
    frameworkRightsLanguageEqualsLocalImplementationIsFalse : frameworkRightsLanguageEqualsLocalImplementation ≡ false
    recognitionOfTerritoryTransfersCommunityAuthorityToConservationAgency : Bool
    recognitionOfTerritoryTransfersCommunityAuthorityToConservationAgencyIsFalse : recognitionOfTerritoryTransfersCommunityAuthorityToConservationAgency ≡ false

canonicalTarget3Boundary : Target3Boundary
canonicalTarget3Boundary = target3Boundary false refl false refl false refl
