module DASHI.Governance.SteffensenCulturalFireAuthorityExact where

open import DASHI.Core.Prelude
import DASHI.Core.KnowledgeContentAuthoritySeparationExact as Core
import DASHI.Governance.IndigenousEnvironmentalJusticeSourceRegistryExact as Sources

------------------------------------------------------------------------
-- CULTURAL FIRE: KNOWLEDGE / PRACTICE / AUTHORITY
--
-- Victor Steffensen, Fire Country (2020), ISBN 9781741177268.
-- Firesticks Alliance Indigenous Corporation, NSW Bushfire Inquiry submission
-- 0906 (2020).
--
-- Source-bounded claim: cultural-fire knowledge and technique do not by
-- themselves create Country-specific cultural authority.  This is not a
-- universal theorem about all Indigenous governance structures.
------------------------------------------------------------------------

data Agent : Set where
  traditionalCustodian trainedExternalPractitioner externalReader : Agent

data Country : Set where
  homeCountry otherCountry : Country

data FireKnowledge : Set where
  culturalBurning : FireKnowledge

data Knows : Agent → FireKnowledge → Set where
  custodianKnows : Knows traditionalCustodian culturalBurning
  trainedKnows : Knows trainedExternalPractitioner culturalBurning
  readerKnows : Knows externalReader culturalBurning

data CanPractice : Agent → Country → FireKnowledge → Set where
  custodianPractices : CanPractice traditionalCustodian homeCountry culturalBurning
  trainedPracticesUnderAuthority : CanPractice trainedExternalPractitioner homeCountry culturalBurning

data CanAuthorize : Agent → Country → FireKnowledge → Set where
  custodianAuthorizes : CanAuthorize traditionalCustodian homeCountry culturalBurning

system : Core.SituatedKnowledgeAuthority Agent Country FireKnowledge
system = Core.situatedKnowledgeAuthority Knows CanPractice CanAuthorize

trainedTechniqueWithoutAuthority : Core.PracticeWithoutAuthority system
trainedTechniqueWithoutAuthority =
  Core.practiceWithoutAuthority
    trainedExternalPractitioner homeCountry culturalBurning
    trainedPracticesUnderAuthority (λ ())

readerContentWithoutAuthority : Core.ContentWithoutAuthority system
readerContentWithoutAuthority =
  Core.contentWithoutAuthority
    externalReader homeCountry culturalBurning readerKnows (λ ())

custodianAuthority : CanAuthorize traditionalCustodian homeCountry culturalBurning
custodianAuthority = custodianAuthorizes

steffensenSource : Sources.SourceReference
steffensenSource = Sources.steffensen2020

firesticksSource : Sources.SourceReference
firesticksSource = Sources.firesticks2020

record CulturalFireAuthorityBoundary : Set where
  constructor culturalFireAuthorityBoundary
  field
    learningTechniqueCreatesCountryAuthority : Bool
    learningTechniqueCreatesCountryAuthorityIsFalse : learningTechniqueCreatesCountryAuthority ≡ false
    externalPublicationCreatesCountryAuthority : Bool
    externalPublicationCreatesCountryAuthorityIsFalse : externalPublicationCreatesCountryAuthority ≡ false
    institutionalSupportEqualsTraditionalCustodianAuthority : Bool
    institutionalSupportEqualsTraditionalCustodianAuthorityIsFalse : institutionalSupportEqualsTraditionalCustodianAuthority ≡ false
    steffensenBookIsUniversalPermissionRule : Bool
    steffensenBookIsUniversalPermissionRuleIsFalse : steffensenBookIsUniversalPermissionRule ≡ false

canonicalCulturalFireAuthorityBoundary : CulturalFireAuthorityBoundary
canonicalCulturalFireAuthorityBoundary = culturalFireAuthorityBoundary false refl false refl false refl false refl
