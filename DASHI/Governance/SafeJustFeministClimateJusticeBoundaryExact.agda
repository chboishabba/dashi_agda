module DASHI.Governance.SafeJustFeministClimateJusticeBoundaryExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- FEMINIST ECONOMICS / FEMINIST CLIMATE JUSTICE SOURCE BOUNDARY
--
-- Bounded source roles only.  The finite witnesses below are DASHI theorem
-- constructions motivated by the cited literature; the authors are not
-- credited with these Nat/Bool encodings.
--
-- Marilyn Waring, If Women Counted (1988); retrospective source:
-- Marilyn Power et al., "Twenty-Five Years of Counting for Nothing:
-- Waring's Critique of National Accounts", Feminist Economics 23(2),
-- DOI 10.1080/13545701.2016.1178854.
--
-- Sherilyn MacGregor, "'Gender and climate change': from impacts to
-- discourses", Journal of the Indian Ocean Region 6(2) (2010),
-- DOI 10.1080/19480881.2010.536669.
-- Sherilyn MacGregor, "Only Resist: Feminist Ecological Citizenship and the
-- Post-politics of Climate Change", Hypatia 29(3) (2014),
-- DOI 10.1111/hypa.12065.
--
-- Farhana Sultana, "The Unbearable Heaviness of Climate Coloniality",
-- Political Geography 99 (2022), 102638,
-- DOI 10.1016/j.polgeo.2022.102638.
--
-- Margaret Alston, Sascha Fuller & Nikita Kwarney,
-- "Women and climate change in Vanuatu, Pacific Islands Region" (2023),
-- DOI 10.1080/0966369X.2023.2229530.
--
-- George Carter & Elise Howard, "Pacific women in climate change
-- negotiations", Small States & Territories 3(2) (2020), 303--318.
--
-- Kathryn Yusoff, A Billion Black Anthropocenes or None (2018),
-- University of Minnesota Press, DOI 10.5749/9781452962054.
--
-- Wangari Maathai, Nobel Peace Prize lecture (2004).
------------------------------------------------------------------------

data FeministClimateSource : Set where
  waring1988
  macgregor2010
  macgregor2014
  sultana2022
  alstonFullerKwarney2023
  carterHoward2020
  yusoff2018
  maathai2004
  : FeministClimateSource

data SourceRole : Set where
  productionBoundaryCritique
  measurableImpactCritique
  postPoliticalAuthorityCritique
  climateColoniality
  situatedLivedOutcome
  hiddenNegotiatingContribution
  categoryNeutralityCritique
  bottomUpSituatedAuthority
  : SourceRole

record SourceRoleEntry : Set where
  constructor sourceRoleEntry
  field
    source : FeministClimateSource
    role : SourceRole

waringRole : SourceRoleEntry
waringRole = sourceRoleEntry waring1988 productionBoundaryCritique

macgregorImpactRole : SourceRoleEntry
macgregorImpactRole = sourceRoleEntry macgregor2010 measurableImpactCritique

macgregorPostPoliticalRole : SourceRoleEntry
macgregorPostPoliticalRole = sourceRoleEntry macgregor2014 postPoliticalAuthorityCritique

sultanaRole : SourceRoleEntry
sultanaRole = sourceRoleEntry sultana2022 climateColoniality

yusoffRole : SourceRoleEntry
yusoffRole = sourceRoleEntry yusoff2018 categoryNeutralityCritique

maathaiRole : SourceRoleEntry
maathaiRole = sourceRoleEntry maathai2004 bottomUpSituatedAuthority

------------------------------------------------------------------------
-- Waring-style production-boundary non-factorability witness.
--
-- countedOutput is a deliberately tiny shadow of a national-accounts observer:
-- an unpaid-care state and a no-activity state both map to zero counted output,
-- while their provisioning contributions differ.
------------------------------------------------------------------------

data ActivityState : Set where
  noActivity unpaidCare paidMarketActivity : ActivityState

countedOutput : ActivityState → Nat
countedOutput noActivity = 0
countedOutput unpaidCare = 0
countedOutput paidMarketActivity = 1

provisioningContribution : ActivityState → Nat
provisioningContribution noActivity = 0
provisioningContribution unpaidCare = 1
provisioningContribution paidMarketActivity = 1

sameCountedOutput : countedOutput noActivity ≡ countedOutput unpaidCare
sameCountedOutput = refl

countedOutputDoesNotRecoverProvisioning :
  provisioningContribution noActivity ≡ provisioningContribution unpaidCare → ⊥
countedOutputDoesNotRecoverProvisioning ()

------------------------------------------------------------------------
-- Climate-justice authority coordinates.
------------------------------------------------------------------------

data ResidualKind : Set where
  phenomenonResidual
  epistemicResidual
  responsibilityImpactAsymmetryResidual
  categoricalAuthorityResidual
  democraticAuthorityResidual
  : ResidualKind

phenomenonResidualDiffersFromEpistemicResidual :
  phenomenonResidual ≡ epistemicResidual → ⊥
phenomenonResidualDiffersFromEpistemicResidual ()

responsibilityResidualDiffersFromDataResidual :
  responsibilityImpactAsymmetryResidual ≡ epistemicResidual → ⊥
responsibilityResidualDiffersFromDataResidual ()

categoricalAuthorityResidualDiffersFromMissingData :
  categoricalAuthorityResidual ≡ epistemicResidual → ⊥
categoricalAuthorityResidualDiffersFromMissingData ()

------------------------------------------------------------------------
-- Source-bounded non-promotions.
------------------------------------------------------------------------

record FeministClimateJusticeBoundary : Set where
  constructor feministClimateJusticeBoundary
  field
    countedEconomicOutputExhaustsProvisioning : Bool
    countedEconomicOutputExhaustsProvisioningIsFalse :
      countedEconomicOutputExhaustsProvisioning ≡ false
    completeIndicatorCoverageCertifiesParticipatoryJustice : Bool
    completeIndicatorCoverageCertifiesParticipatoryJusticeIsFalse :
      completeIndicatorCoverageCertifiesParticipatoryJustice ≡ false
    technicallyQualifiedForecastAuthorizesDepoliticizedAdministration : Bool
    technicallyQualifiedForecastAuthorizesDepoliticizedAdministrationIsFalse :
      technicallyQualifiedForecastAuthorizesDepoliticizedAdministration ≡ false
    completeDataLedgerDischargesResponsibilityImpactAsymmetry : Bool
    completeDataLedgerDischargesResponsibilityImpactAsymmetryIsFalse :
      completeDataLedgerDischargesResponsibilityImpactAsymmetry ≡ false
    completeDataLedgerCertifiesCategoryNeutrality : Bool
    completeDataLedgerCertifiesCategoryNeutralityIsFalse :
      completeDataLedgerCertifiesCategoryNeutrality ≡ false
    formalDelegationVisibilityRecoversActualNegotiatingContribution : Bool
    formalDelegationVisibilityRecoversActualNegotiatingContributionIsFalse :
      formalDelegationVisibilityRecoversActualNegotiatingContribution ≡ false
    ecologicalFunctioningAutomaticallyCreatesDemocraticAuthority : Bool
    ecologicalFunctioningAutomaticallyCreatesDemocraticAuthorityIsFalse :
      ecologicalFunctioningAutomaticallyCreatesDemocraticAuthority ≡ false

canonicalFeministClimateJusticeBoundary : FeministClimateJusticeBoundary
canonicalFeministClimateJusticeBoundary =
  feministClimateJusticeBoundary
    false refl false refl false refl false refl false refl false refl false refl
