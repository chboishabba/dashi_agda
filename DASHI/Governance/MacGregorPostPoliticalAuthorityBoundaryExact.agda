module DASHI.Governance.MacGregorPostPoliticalAuthorityBoundaryExact where

open import DASHI.Core.Prelude
import DASHI.Core.PoliticalContestabilityExact as Political
import DASHI.Governance.SafeJustQualifiedClaimPromotionExact as Promotion
import DASHI.Governance.FeministClimateJusticeSourceRegistryExact as Sources

------------------------------------------------------------------------
-- MACGREGOR: TECHNICAL ADEQUACY != POLITICAL CONTESTABILITY
--
-- Sherilyn MacGregor, "Only Resist: Feminist Ecological Citizenship and the
-- Post-politics of Climate Change", Hypatia 29(3), 617-633 (2014).
-- DOI: 10.1111/hypa.12065.
--
-- Source calibration: critique of climate narratives that replace democratic
-- public debate with expert administration / individual behaviour change.
-- DASHI does not infer that expertise or administration is inherently invalid.
------------------------------------------------------------------------

data ClimateAlternative : Set where
  technocraticPath democraticDeliberationPath : ClimateAlternative

data ClimateParticipant : Set where affectedPublic : ClimateParticipant

data CanContestClimate : ClimateParticipant → ClimateAlternative → Set where
  contestDemocraticPath : CanContestClimate affectedPublic democraticDeliberationPath

data CanSetClimateAgenda : ClimateParticipant → Set where
  affectedPublicSetsAgenda : CanSetClimateAgenda affectedPublic

data CanDeliberateClimate : ClimateParticipant → Set where
  affectedPublicDeliberates : CanDeliberateClimate affectedPublic

climateContestability : Political.PoliticalContestability
climateContestability =
  Political.politicalContestability
    ClimateAlternative ClimateParticipant
    CanContestClimate CanSetClimateAgenda CanDeliberateClimate

democraticContestabilityReceipt : Political.ContestabilityReceipt climateContestability
democraticContestabilityReceipt =
  Political.contestabilityReceipt
    affectedPublic democraticDeliberationPath
    contestDemocraticPath affectedPublicSetsAgenda affectedPublicDeliberates

-- #625 already supplies a qualified empirical-synthesis promotion.  It remains
-- technically/evidentially qualified while carrying residuals; this module adds
-- the separate political-contestability axis rather than redefining promotion.
qualifiedSynthesisExists : Promotion.QualifiedSynthesisPromotion
qualifiedSynthesisExists = Promotion.canonicalQualifiedSynthesisPromotion

data DepoliticizedAdministrativeMandate : Set where

qualifiedSynthesisDoesNotSupplyDepoliticizedMandate :
  DepoliticizedAdministrativeMandate → ⊥
qualifiedSynthesisDoesNotSupplyDepoliticizedMandate ()

source : Sources.SourceReference
source = Sources.macGregor2014

record MacGregorPostPoliticalBoundary : Set where
  constructor macGregorPostPoliticalBoundary
  field
    consumerAdequateEvidenceImpliesPoliticalContestability : Bool
    consumerAdequateEvidenceImpliesPoliticalContestabilityIsFalse :
      consumerAdequateEvidenceImpliesPoliticalContestability ≡ false
    qualifiedSynthesisImpliesDepoliticizedAdministrativeMandate : Bool
    qualifiedSynthesisImpliesDepoliticizedAdministrativeMandateIsFalse :
      qualifiedSynthesisImpliesDepoliticizedAdministrativeMandate ≡ false
    expertEvidenceIsInvalidByDefinition : Bool
    expertEvidenceIsInvalidByDefinitionIsFalse : expertEvidenceIsInvalidByDefinition ≡ false
    politicalContestabilityEqualsLegitimacy : Bool
    politicalContestabilityEqualsLegitimacyIsFalse :
      politicalContestabilityEqualsLegitimacy ≡ false

canonicalMacGregorPostPoliticalBoundary : MacGregorPostPoliticalBoundary
canonicalMacGregorPostPoliticalBoundary =
  macGregorPostPoliticalBoundary false refl false refl false refl false refl
