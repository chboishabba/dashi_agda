module DASHI.Economics.AIChinaTSMCGeoEconomicCalibration2026Exact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Economics.AICurrentRegimeCalibration2026Exact as AI
import DASHI.Economics.AICurrentRegimePromotionSchedulerExact as Scheduler
import DASHI.Economics.CUDAROCmTSMCManufacturingCrossPollinationExact as TSMC

------------------------------------------------------------------------
-- AI / CHINA / TSMC GEO-ECONOMIC CALIBRATION, SEPTEMBER 2026
--
-- Manufacturing dominance, supply-chain leverage, AI capex lock-in and TSMC
-- geographic diversification are distinct coordinates.  None alone proves a
-- "winner", a bubble, or Taiwan's political status.
------------------------------------------------------------------------

imfChinaDominance2025 : Source.AttributedSource
imfChinaDominance2025 = Source.mkNoDOISource
  "International Monetary Fund"
  "Spillovers from Large Emerging Economies: How Dominant Is China?"
  "IMF Working Paper WP/25/27"
  "2025"
  "https://www.imf.org/-/media/Files/Publications/WP/2025/English/wpiea2025027-print-pdf.ashx"
  Source.institutionalSource
  "source for China's manufacturing and trade scale: roughly 35% of global manufacturing gross production, 29% of value added, and broad global trade centrality"
  Source.publicAttribution

imfChinaEngine2026 : Source.AttributedSource
imfChinaEngine2026 = Source.mkNoDOISource
  "International Monetary Fund"
  "China's Emerging Economic Engine"
  "Finance & Development"
  "2026-09"
  "https://www.imf.org/en/publications/fandd/issues/2026/09/chinas-emerging-economic-engine-yanliang-miao"
  Source.institutionalSource
  "source for diversification of Chinese trade, high-tech export growth and industrial upgrading under geopolitical fragmentation"
  Source.publicAttribution

imfChinaArticleIV2026 : Source.AttributedSource
imfChinaArticleIV2026 = Source.mkNoDOISource
  "International Monetary Fund"
  "IMF Executive Board Concludes 2025 Article IV Consultation with China"
  "IMF Press Release 26/053"
  "2026-02-18"
  "https://www.imf.org/en/news/articles/2026/02/18/pr-26053-china-imf-executive-board-concludes-2025-article-iv-consultation"
  Source.institutionalSource
  "countervailing source for resilient growth and exports alongside weak private domestic demand, muted inflation and structural imbalance"
  Source.publicAttribution

anthropicCapexReuters2026 : Source.AttributedSource
anthropicCapexReuters2026 = Source.mkNoDOISource
  "Reuters"
  "Anthropic's $518 billion AI buildout hinges largely on deals that cannot be canceled, filing shows"
  "Reuters"
  "2026-09-29"
  "https://www.reuters.com/business/anthropics-518-billion-ai-buildout-hinges-largely-deals-that-cannot-be-canceled-2026-09-29/"
  Source.newsSource
  "secondary source for reported long-horizon, largely non-cancelable AI infrastructure commitments; capital lock-in is not bubble classification"
  Source.publicAttribution

tsmcTexasReuters2026 : Source.AttributedSource
tsmcTexasReuters2026 = Source.mkNoDOISource
  "Reuters"
  "TSMC evaluates potential Texas investment, sources say"
  "Reuters"
  "2026-09-30"
  "https://www.reuters.com/world/asia-pacific/tsmc-evaluates-potential-texas-investment-sources-say-2026-09-30/"
  Source.newsSource
  "secondary source for possible Texas expansion in addition to the large Arizona buildout; geographic diversification is not political-status adjudication"
  Source.publicAttribution

data GeoEconomicCoordinate : Set where
  manufacturingScale : GeoEconomicCoordinate
  exportNetworkCentrality : GeoEconomicCoordinate
  highTechIndustrialUpgrade : GeoEconomicCoordinate
  domesticDemandStrength : GeoEconomicCoordinate
  reserveCurrencyPower : GeoEconomicCoordinate
  aiCapitalLockIn : GeoEconomicCoordinate
  semiconductorFoundryConcentration : GeoEconomicCoordinate
  semiconductorGeographicDiversification : GeoEconomicCoordinate

record GeoEconomicObservation : Set where
  constructor geo-economic-observation
  field
    coordinate : GeoEconomicCoordinate
    reading : String
    source : Source.AttributedSource
    supportsGlobalLeadershipDimension : Bool
    provesOverallEconomicLeadership : Bool
    provesAIInfrastructureBubble : Bool
    provesTaiwanPoliticalStatus : Bool

open GeoEconomicObservation public

chinaManufacturingScale : GeoEconomicObservation
chinaManufacturingScale = geo-economic-observation
  manufacturingScale
  "China is the world's dominant manufacturing hub by gross production and value-added scale."
  imfChinaDominance2025
  true false false false

chinaDomesticDemandResidual : GeoEconomicObservation
chinaDomesticDemandResidual = geo-economic-observation
  domesticDemandStrength
  "Private domestic demand remains comparatively weak despite resilient output and exports."
  imfChinaArticleIV2026
  false false false false

anthropicLockIn : GeoEconomicObservation
anthropicLockIn = geo-economic-observation
  aiCapitalLockIn
  "Reported long-term non-cancelable compute/infrastructure obligations create capital lock-in exposure."
  anthropicCapexReuters2026
  false false false false

tsmcDiversification : GeoEconomicObservation
tsmcDiversification = geo-economic-observation
  semiconductorGeographicDiversification
  "TSMC is considering further U.S. geographic diversification beyond Arizona."
  tsmcTexasReuters2026
  false false false false

existingAICalibration : AI.AICurrentRegimeCalibration2026
existingAICalibration = AI.canonicalAICurrentRegimeCalibration2026

bubbleResidualStillOpen : Scheduler.PromotionResidual
bubbleResidualStillOpen = Scheduler.bubbleResidual

data ManufacturingDominanceMeansEconomicVictory : Set where
data CapitalLockInMeansBubble : Set where
data TSMCUSInvestmentErasesTaiwanChokepoint : Set where
data ChineseScaleMeansNoStructuralWeakness : Set where

manufacturingDominanceDoesNotProveOverallVictory :
  ManufacturingDominanceMeansEconomicVictory → ⊥
manufacturingDominanceDoesNotProveOverallVictory ()

capitalLockInDoesNotByItselfProveBubble : CapitalLockInMeansBubble → ⊥
capitalLockInDoesNotByItselfProveBubble ()

tsmcUSInvestmentDoesNotEraseTaiwanRole :
  TSMCUSInvestmentErasesTaiwanChokepoint → ⊥
tsmcUSInvestmentDoesNotEraseTaiwanChokepoint ()

scaleDoesNotEraseStructuralWeakness :
  ChineseScaleMeansNoStructuralWeakness → ⊥
scaleDoesNotEraseStructuralWeakness ()
