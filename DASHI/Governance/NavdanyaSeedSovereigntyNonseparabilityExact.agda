module DASHI.Governance.NavdanyaSeedSovereigntyNonseparabilityExact where

open import DASHI.Core.Prelude
import DASHI.Governance.IndigenousEnvironmentalJusticeSourceRegistryExact as Sources

------------------------------------------------------------------------
-- NAVDANYA / SEED FREEDOM: GERMPLASM != SOVEREIGNTY
--
-- Primary institutional source: Navdanya International,
-- Seed Freedom: A Global Citizens' Report (2012).
--
-- The source motivates keeping biological seed material, saving/exchange,
-- community control, biodiversity and intergenerational transmission separate.
-- The finite carrier below is a DASHI construction, not a quantitative theorem
-- attributed to Navdanya or Vandana Shiva.
------------------------------------------------------------------------

data SeedState : Set where
  enclosedSeed communitySeed : SeedState

data GermplasmCode : Set where sameSeedMaterial : GermplasmCode

data CommunityControl : Set where controlledExternally controlledByCommunity : CommunityControl

data ExchangeFreedom : Set where exchangeRestricted exchangeOpen : ExchangeFreedom

data BiodiversityRelation : Set where biodiversityNarrow biodiversityMaintained : BiodiversityRelation

germplasm : SeedState → GermplasmCode
germplasm _ = sameSeedMaterial

control : SeedState → CommunityControl
control enclosedSeed = controlledExternally
control communitySeed = controlledByCommunity

exchange : SeedState → ExchangeFreedom
exchange enclosedSeed = exchangeRestricted
exchange communitySeed = exchangeOpen

biodiversityRelation : SeedState → BiodiversityRelation
biodiversityRelation enclosedSeed = biodiversityNarrow
biodiversityRelation communitySeed = biodiversityMaintained

sameMaterial : germplasm enclosedSeed ≡ germplasm communitySeed
sameMaterial = refl

sameMaterialDoesNotRecoverControl : control enclosedSeed ≡ control communitySeed → ⊥
sameMaterialDoesNotRecoverControl ()

sameMaterialDoesNotRecoverExchange : exchange enclosedSeed ≡ exchange communitySeed → ⊥
sameMaterialDoesNotRecoverExchange ()

sameMaterialDoesNotRecoverBiodiversityRelation :
  biodiversityRelation enclosedSeed ≡ biodiversityRelation communitySeed → ⊥
sameMaterialDoesNotRecoverBiodiversityRelation ()

source : Sources.SourceReference
source = Sources.navdanya2012

record SeedSovereigntyBoundary : Set where
  constructor seedSovereigntyBoundary
  field
    sameGermplasmImpliesSameCommunityControl : Bool
    sameGermplasmImpliesSameCommunityControlIsFalse : sameGermplasmImpliesSameCommunityControl ≡ false
    seedMaterialExhaustsSeedSovereignty : Bool
    seedMaterialExhaustsSeedSovereigntyIsFalse : seedMaterialExhaustsSeedSovereignty ≡ false
    patentStatusAloneDeterminesFoodSecurity : Bool
    patentStatusAloneDeterminesFoodSecurityIsFalse : patentStatusAloneDeterminesFoodSecurity ≡ false
    institutionalDeclarationIsUniversalAgronomicLaw : Bool
    institutionalDeclarationIsUniversalAgronomicLawIsFalse : institutionalDeclarationIsUniversalAgronomicLaw ≡ false

canonicalSeedSovereigntyBoundary : SeedSovereigntyBoundary
canonicalSeedSovereigntyBoundary = seedSovereigntyBoundary false refl false refl false refl false refl
