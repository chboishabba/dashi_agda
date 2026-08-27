module DASHI.Governance.BudjBimAquacultureAuthorityExact where

open import DASHI.Core.Prelude
import DASHI.Governance.EnvironmentalAuthoritySourceRegistryRound2Exact as Sources

------------------------------------------------------------------------
-- BUDJ BIM: INDEPENDENT GUNDITJMARA AQUACULTURE / HYDROLOGICAL-ENGINEERING
-- EVIDENCE, NOT A DERIVATIVE DARK EMU CLAIM.
--
-- UNESCO World Heritage property 1577 records deliberate modification of
-- waterways/wetlands, channels/weirs/dams, systematic trapping/storage/harvest
-- of kooyang, at least 6600 years of hydrological/ecological management, a
-- six-millennia economic/social base, continuing Gunditjmara knowledge and
-- Aboriginal ownership/management.
------------------------------------------------------------------------

data BudjBimEvidence : Set where
  deliberateHydrologicalEngineering
  systematicKooyangAquaculture
  sixMillenniaEconomicSocialBase
  continuingGunditjmaraKnowledge
  : BudjBimEvidence

data EvidenceAuthority : BudjBimEvidence → Set where
  unescoEngineering : EvidenceAuthority deliberateHydrologicalEngineering
  unescoAquaculture : EvidenceAuthority systematicKooyangAquaculture
  unescoEconomicBase : EvidenceAuthority sixMillenniaEconomicSocialBase
  unescoContinuity : EvidenceAuthority continuingGunditjmaraKnowledge

source : Sources.SourceReference
source = Sources.unescoBudjBim2019

record BudjBimBoundary : Set where
  constructor budjBimBoundary
  field
    evidenceDependsOnPascoeFraming : Bool
    evidenceDependsOnPascoeFramingIsFalse : evidenceDependsOnPascoeFraming ≡ false
    aquacultureEvidenceSettlesEveryAgricultureLabel : Bool
    aquacultureEvidenceSettlesEveryAgricultureLabelIsFalse : aquacultureEvidenceSettlesEveryAgricultureLabel ≡ false
    UNESCOListingTransfersGunditjmaraAuthorityToExternalAuthors : Bool
    UNESCOListingTransfersGunditjmaraAuthorityToExternalAuthorsIsFalse : UNESCOListingTransfersGunditjmaraAuthorityToExternalAuthors ≡ false
    economicSocialBaseAloneProvesEveryVillageClaim : Bool
    economicSocialBaseAloneProvesEveryVillageClaimIsFalse : economicSocialBaseAloneProvesEveryVillageClaim ≡ false

canonicalBudjBimBoundary : BudjBimBoundary
canonicalBudjBimBoundary = budjBimBoundary false refl false refl false refl false refl
