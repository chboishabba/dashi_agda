module DASHI.Governance.IndigenousEnvironmentalAuthorityRegression where

open import DASHI.Core.Prelude
import DASHI.Governance.IndigenousEnvironmentalAuthorityCapstoneExact as Capstone
import DASHI.Governance.CaceresAuthorityWithoutEnforcementExact as Caceres
import DASHI.Governance.IPCCAR6IndigenousKnowledgeIntegrationAuditExact as IPCC
import DASHI.Governance.NavdanyaSeedSovereigntyNonseparabilityExact as Seed
import DASHI.Governance.NativeTitleAuthorityLayerExact as NativeTitle

communityNotLegalCorporation :
  NativeTitle.traditionalOwnerCommunity ≡ NativeTitle.registeredNativeTitleBodyCorporate → ⊥
communityNotLegalCorporation = Capstone.traditionalOwnerCommunityIsNotRntbc

victimRecognitionNotEnforcement :
  Caceres.EffectiveEnforcement Caceres.victimStanding → ⊥
victimRecognitionNotEnforcement = Capstone.recognizedVictimStandingDoesNotConstructEnforcement

wgiiIndigenousAuthorshipReceipt :
  IPCC.integration IPCC.wgIIChapter14 IPCC.indigenousKnowledge ≡ IPCC.indigenousAuthorship
wgiiIndigenousAuthorshipReceipt = Capstone.ipccIntegrationIsUneven

seedMaterialNotCommunityControl :
  Seed.control Seed.enclosedSeed ≡ Seed.control Seed.communitySeed → ⊥
seedMaterialNotCommunityControl = Capstone.sameSeedMaterialDoesNotRecoverCommunityControl
