module DASHI.Governance.IndigenousEnvironmentalAuthorityCapstoneExact where

open import DASHI.Core.Prelude
import DASHI.Core.RecognitionConstitutionNonfactorabilityExact as Recognition
import DASHI.Governance.IndigenousAuthorityEnvelopeExact as Envelope
import DASHI.Governance.CulturalFireAuthorityEnvelopeBridgeExact as Fire
import DASHI.Governance.NativeTitleAuthorityLayerExact as NativeTitle
import DASHI.Governance.IPCCAR6IndigenousKnowledgeIntegrationAuditExact as IPCC
import DASHI.Governance.CaceresAuthorityWithoutEnforcementExact as Caceres
import DASHI.Governance.NavdanyaSeedSovereigntyNonseparabilityExact as Seed
import DASHI.Governance.MoretonRobinsonRecognitionSovereigntyBoundaryExact as Moreton
import DASHI.Governance.FirstNationsOwnedEvidenceContractExact as Evidence

------------------------------------------------------------------------
-- INDIGENOUS / ENVIRONMENTAL AUTHORITY CAPSTONE
--
-- Keeps knowledge content, cultural permission, legal representation,
-- recognition, enforcement, scientific-assessment inclusion and commons control
-- as separate authority coordinates.
------------------------------------------------------------------------

culturalFireTechniqueDoesNotTransferAuthority :
  Envelope.AuthorityEnvelope.sovereignStanding Fire.externalTechniqueEnvelope ≡
  Envelope.originatingAuthority → ⊥
culturalFireTechniqueDoesNotTransferAuthority = Fire.externalTechniqueIsNotOriginatingAuthority

traditionalOwnerCommunityIsNotRntbc :
  NativeTitle.traditionalOwnerCommunity ≡ NativeTitle.registeredNativeTitleBodyCorporate → ⊥
traditionalOwnerCommunityIsNotRntbc = NativeTitle.communityIsNotRntbc

ipccIntegrationIsUneven :
  IPCC.integration IPCC.wgIIChapter14 IPCC.indigenousKnowledge ≡ IPCC.indigenousAuthorship
ipccIntegrationIsUneven = IPCC.wgiiChapter14StrongerThanWgi

recognizedVictimStandingDoesNotConstructEnforcement :
  Caceres.EffectiveEnforcement Caceres.victimStanding → ⊥
recognizedVictimStandingDoesNotConstructEnforcement = Caceres.victimStandingDoesNotConstructEnforcement

sameSeedMaterialDoesNotRecoverCommunityControl :
  Seed.control Seed.enclosedSeed ≡ Seed.control Seed.communitySeed → ⊥
sameSeedMaterialDoesNotRecoverCommunityControl = Seed.sameMaterialDoesNotRecoverControl

settlerRecognitionDoesNotExhaustSovereignty :
  Recognition.FactorsThroughRecognition Moreton.recognitionSystem → ⊥
settlerRecognitionDoesNotExhaustSovereignty = Moreton.settlerRecognitionCannotExhaustSovereignAuthority

externalHistoricalSourceDoesNotCreateLandAuthority :
  Evidence.AuthorizedFor Evidence.externalHistoricalReconstruction Evidence.landManagementAuthority → ⊥
externalHistoricalSourceDoesNotCreateLandAuthority = Evidence.externalHistorianDoesNotBecomeLandManagementAuthority

record IndigenousEnvironmentalAuthorityBoundary : Set where
  constructor indigenousEnvironmentalAuthorityBoundary
  field
    knowledgeContentEqualsCulturalPermission : Bool
    knowledgeContentEqualsCulturalPermissionIsFalse : knowledgeContentEqualsCulturalPermission ≡ false
    communityAuthorityEqualsSettlerLegalCorporation : Bool
    communityAuthorityEqualsSettlerLegalCorporationIsFalse : communityAuthorityEqualsSettlerLegalCorporation ≡ false
    institutionalRecognitionEqualsEffectiveEnforcement : Bool
    institutionalRecognitionEqualsEffectiveEnforcementIsFalse : institutionalRecognitionEqualsEffectiveEnforcement ≡ false
    scientificAssessmentInclusionEqualsKnowledgeSovereignty : Bool
    scientificAssessmentInclusionEqualsKnowledgeSovereigntyIsFalse : scientificAssessmentInclusionEqualsKnowledgeSovereignty ≡ false
    biologicalMaterialEqualsSeedSovereignty : Bool
    biologicalMaterialEqualsSeedSovereigntyIsFalse : biologicalMaterialEqualsSeedSovereignty ≡ false
    externalDocumentationEqualsOriginatingAuthority : Bool
    externalDocumentationEqualsOriginatingAuthorityIsFalse : externalDocumentationEqualsOriginatingAuthority ≡ false

canonicalIndigenousEnvironmentalAuthorityBoundary : IndigenousEnvironmentalAuthorityBoundary
canonicalIndigenousEnvironmentalAuthorityBoundary =
  indigenousEnvironmentalAuthorityBoundary false refl false refl false refl false refl false refl false refl
