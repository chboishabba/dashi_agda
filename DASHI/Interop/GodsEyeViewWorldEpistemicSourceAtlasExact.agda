module DASHI.Interop.GodsEyeViewWorldEpistemicSourceAtlasExact where

open import DASHI.Core.Prelude

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.EmpiricalSourceDiligenceAdmissionExact as Diligence

------------------------------------------------------------------------
-- TYPED SOURCE ATLAS FOR THE PUBLIC-INTEREST WORLD EPISTEMIC LANE
--
-- These are recoverable bibliographic/source identities for empirical claims
-- already used by the GEV/activist/LES/market cross-pollination.  Their presence
-- does not import proof, truth, applicability, legal judgment, or intervention
-- authority.  Each downstream proposition must still attach an exact span or
-- locator and SourceDiligence.
------------------------------------------------------------------------

heritageProject2025Primary : Source.AttributedSource
heritageProject2025Primary = Source.mkNoDOISource
  "Paul Dans and Steven Groves (eds.)"
  "Mandate for Leadership: The Conservative Promise"
  "The Heritage Foundation / 2025 Presidential Transition Project"
  "2023"
  "https://static.heritage.org/project2025/2025_MandateForLeadership_FULL.pdf"
  Source.institutionalSource
  "primary publication carrier for chapter-specific Project 2025 recommendations; later administration implementation requires separate primary evidence"
  Source.publicAttribution

cftcPredictionMarketAdvisory2026 : Source.AttributedSource
cftcPredictionMarketAdvisory2026 = Source.mkNoDOISource
  "Commodity Futures Trading Commission, Division of Enforcement"
  "CFTC Enforcement Division Issues Prediction Markets Advisory"
  "CFTC Release 9185-26"
  "2026"
  "https://www.cftc.gov/PressRoom/PressReleases/9185-26"
  Source.governmentSource
  "primary regulator source establishing 2026 prediction-market enforcement examples and nonpublic-information/outcome-influence concerns; not guilt of other traders"
  Source.publicAttribution

kalshiInsiderTradingPolicy : Source.AttributedSource
kalshiInsiderTradingPolicy = Source.mkNoDOISource
  "Kalshi"
  "Stopping insider trading"
  "Kalshi Policy Center"
  "2026"
  "https://kalshi.com/policy-center/insider-trading"
  Source.practitionerSource
  "primary venue policy/monitoring account; venue policy does not itself establish statutory liability"
  Source.publicAttribution

wmoOzoneBulletin2025 : Source.AttributedSource
wmoOzoneBulletin2025 = Source.mkNoDOISource
  "World Meteorological Organization"
  "WMO Ozone and UV Bulletin No. 3 – September 2025"
  "WMO Global Atmosphere Watch"
  "2025"
  "https://wmo.int/resources/publication-series/wmo-ozone-and-uv-bulletin/wmo-ozone-and-uv-bulletin-no-3-september-2025"
  Source.institutionalSource
  "official synthesis for ozone recovery, variability and monitoring; not a local climate-causation source"
  Source.publicAttribution

dongPolvaniHwangEngland2025 : Source.AttributedSource
dongPolvaniHwangEngland2025 = Source.mkDOISource
  "Yue Dong; Lorenzo M. Polvani; Yen-Ting Hwang; Mark R. England et al."
  "Stratospheric ozone depletion has contributed to the recent tropical La Niña-like cooling pattern"
  "npj Climate and Atmospheric Science 8, Article 150"
  "2025"
  "10.1038/s41612-025-01020-0"
  "https://www.nature.com/articles/s41612-025-01020-0"
  Source.academicArticleSource
  "peer-reviewed mechanism evidence for an ozone-depletion contribution to a tropical SST pattern; not a universal ozone/climate sign theorem"
  Source.publicAttribution

friedelChiodoWeberEtAl2026 : Source.AttributedSource
friedelChiodoWeberEtAl2026 = Source.mkDOISource
  "M. Friedel; G. Chiodo; K. Weber; L. M. Polvani; J. S. Daniel et al."
  "Confirming the substantial contribution of ozone-depleting halocarbon emissions to global warming during the second half of the 20th century"
  "npj Climate and Atmospheric Science 9, Article 106"
  "2026"
  "10.1038/s41612-026-01398-5"
  "https://www.nature.com/articles/s41612-026-01398-5"
  Source.academicArticleSource
  "peer-reviewed multimodel evidence that ozone-loss cooling only partially offsets positive halocarbon forcing; distinct from local attribution"
  Source.publicAttribution

worldEpistemicSourceAtlas : Source.AttributedSourceAtlas
worldEpistemicSourceAtlas = Source.mkSourceAtlas
  "GEV public-interest world epistemic source atlas"
  "DASHI.Interop.GodsEyeViewWorldEpistemicSourceAtlasExact"
  (heritageProject2025Primary
    ∷ cftcPredictionMarketAdvisory2026
    ∷ kalshiInsiderTradingPolicy
    ∷ wmoOzoneBulletin2025
    ∷ dongPolvaniHwangEngland2025
    ∷ friedelChiodoWeberEtAl2026
    ∷ [])
  "typed source identities supporting Project 2025, prediction-market and ozone/climate source-diligence lanes; exact claim spans remain downstream obligations"

cftcDiligenceTemplate : Diligence.SourceDiligence
cftcDiligenceTemplate = Diligence.source-diligence
  "CFTC issued a prediction-market enforcement advisory after public enforcement cases involving misuse of nonpublic information/fraud"
  cftcPredictionMarketAdvisory2026
  Diligence.primaryProposition
  true refl
  "searched CFTC primary release number/title and selected the regulator release"
  Diligence.primaryLocated
  "Release 9185-26, opening paragraphs and enumerated enforcement examples"
  "2026-02-25"
  "same CFTC release and KalshiEX/event-contract context"
  "date-bounded 2026 advisory"
  "public regulator release; does not enumerate all prediction-market conduct"
  "venue/regulator and alternative lawful explanations remain separately inspectable"
  "DASHI records the advisory's bounded propositions; it does not infer guilt of an unnamed trader"
  "legal liability requires trader-specific facts and applicable law"

record WorldEpistemicSourceAtlasBoundary : Set where
  constructor world-epistemic-source-atlas-boundary
  field
    typedSourceIdentityReplacesExactClaimLocator : Bool
    typedSourceIdentityReplacesExactClaimLocatorIsFalse :
      typedSourceIdentityReplacesExactClaimLocator ≡ false
    doiCreatesScientificTruth : Bool
    doiCreatesScientificTruthIsFalse : doiCreatesScientificTruth ≡ false
    primaryInstitutionalSourceCreatesNeutralViewFromNowhere : Bool
    primaryInstitutionalSourceCreatesNeutralViewFromNowhereIsFalse :
      primaryInstitutionalSourceCreatesNeutralViewFromNowhere ≡ false

canonicalWorldEpistemicSourceAtlasBoundary : WorldEpistemicSourceAtlasBoundary
canonicalWorldEpistemicSourceAtlasBoundary =
  world-epistemic-source-atlas-boundary false refl false refl false refl
