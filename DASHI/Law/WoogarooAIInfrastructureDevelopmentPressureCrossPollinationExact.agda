module DASHI.Law.WoogarooAIInfrastructureDevelopmentPressureCrossPollinationExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Law.SensibLawWoogarooSwanbankDataCentreDevelopmentPressureExact as Woogaroo
import DASHI.Economics.AIChinaTSMCGeoEconomicCalibration2026Exact as Geo

------------------------------------------------------------------------
-- WOOGAROO / SWANBANK x NATIONAL AI INFRASTRUCTURE BUILDOUT
------------------------------------------------------------------------

anthropicAustraliaReuters2026 : Source.AttributedSource
anthropicAustraliaReuters2026 = Source.mkNoDOISource
  "Reuters"
  "Anthropic signs first Australia data centre agreement"
  "Reuters"
  "2026-09-16"
  "https://www.reuters.com/world/asia-pacific/anthropic-signs-first-australia-data-centre-agreement-2026-09-16/"
  Source.newsSource
  "secondary source for Anthropic's first Australian data-centre lease, a proposed 2.16 GW Queensland campus for inference, subject to approvals"
  Source.publicAttribution

westernDownsABC2026 : Source.AttributedSource
westernDownsABC2026 = Source.mkNoDOISource
  "Australian Broadcasting Corporation"
  "AI giant Anthropic signs agreement for $32b Queensland data centre"
  "ABC News"
  "2026-09-16"
  "https://www.abc.net.au/news/2026-09-16/queensland-data-centre-anthropic-dalby/107160640"
  Source.newsSource
  "secondary source for the proposed Western Downs Digital Park scale and Anthropic lease; this site is not the Swanbank proposal"
  Source.publicAttribution

record AIInfrastructurePressureBridge : Set where
  constructor ai-infrastructure-pressure-bridge
  field
    localDevelopmentWitness : Woogaroo.DevelopmentPressureWitness
    nationalBuildoutSource : Source.AttributedSource
    capitalLockInObservation : Geo.GeoEconomicObservation
    sameProject : Bool
    sameDeveloper : Bool
    sameEnvironmentalFootprint : Bool
    broaderInfrastructureDemandPressureRelevant : Bool
    provesWoogarooCausation : Bool

open AIInfrastructurePressureBridge public

canonicalBridge : AIInfrastructurePressureBridge
canonicalBridge = ai-infrastructure-pressure-bridge
  Woogaroo.swanbankDataCentre
  anthropicAustraliaReuters2026
  Geo.anthropicLockIn
  false false false true false

data NationalAIBoomMeansSwanbankAnthropicProject : Set where
data SameStateMeansSameEcologicalImpact : Set where
data CapitalLockInMeansLocalApproval : Set where

nationalAIBoomDoesNotIdentifySwanbankProject :
  NationalAIBoomMeansSwanbankAnthropicProject → ⊥
nationalAIBoomDoesNotIdentifySwanbankProject ()

sameStateDoesNotMeanSameEcologicalImpact :
  SameStateMeansSameEcologicalImpact → ⊥
sameStateDoesNotMeanSameEcologicalImpact ()

capitalLockInDoesNotDetermineLocalApproval :
  CapitalLockInMeansLocalApproval → ⊥
capitalLockInDoesNotDetermineLocalApproval ()
