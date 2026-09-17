module DASHI.Biology.Agriculture.SudangrassNurseCoverCropExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attribution

kaneko2023DOI : String
kaneko2023DOI = "10.1111/grs.12391"

guretzky2021DOI : String
guretzky2021DOI = "10.3390/agronomy11122449"

burt2025DOI : String
burt2025DOI = "10.1002/cft2.70055"

kanekoEtAl2023 : Attribution.AttributedSource
kanekoEtAl2023 = Attribution.mkDOISource
  "M. Kaneko; et al."
  "Hybrid brachiariagrass establishment with annual sorghum sudangrass and sunn hemp mixtures at half and full recommended seeding rates"
  "Grassland Science"
  "2023" kaneko2023DOI "https://doi.org/10.1111/grs.12391"
  Attribution.academicArticleSource
  "Agricultural pasture-establishment source using sorghum-sudangrass as an annual companion during slow perennial brachiariagrass establishment. Establishment-year cover/forage function is retained separately from perennial trajectory."
  Attribution.publicAttribution

guretzkyRedfearn2021 : Attribution.AttributedSource
guretzkyRedfearn2021 = Attribution.mkDOISource
  "John A. Guretzky; Daren D. Redfearn"
  "Seeding Rate Effects on Forage Mass and Vegetation Dynamics of Cool-Season Grass Sod Interseeded with Sorghum-Sudangrass"
  "Agronomy 11(12):2449"
  "2021" guretzky2021DOI "https://doi.org/10.3390/agronomy11122449"
  Attribution.academicArticleSource
  "Nebraska pasture source. Sorghum-sudangrass increased establishment-year forage mass with seeding rate, while one-time interseeding showed no residual effect on subsequent forage mass/vegetation dynamics."
  Attribution.publicAttribution

burtEtAl2025 : Attribution.AttributedSource
burtEtAl2025 = Attribution.mkDOISource
  "Justin C. Burt; Kathy J. Soder; Kelly M. Mercier; et al."
  "Interseeding crabgrass and berseem clover into sorghum-sudangrass for improved herbage accumulation, nutritive value, and weed suppression"
  "Crop, Forage & Turfgrass Management 11"
  "2025" burt2025DOI "https://doi.org/10.1002/cft2.70055"
  Attribution.academicArticleSource
  "Agricultural forage-mixture source. Herbage accumulation and weed suppression are retained as management functions, not biodiversity or native-restoration endpoints."
  Attribution.publicAttribution

record SudangrassBoundary : Set where
  constructor sudangrass-boundary
  field
    temporaryCoverImpliesPerennialRecovery : Bool
    biomassIncreaseImpliesBiodiversityRecovery : Bool
    weedSuppressionImpliesNativeRestoration : Bool
    annualForageGainImpliesLongTermPastureGain : Bool
    agriculturalPastureResultCreatesNativeGrasslandSameObject : Bool
    terminationAndReversibilityMustRemainIndexed : Bool
    seedingRateAndMixtureMustRemainIndexed : Bool
    precipitationAndSiteContextMustRemainIndexed : Bool
    nurseFunctionCreatesDeploymentAuthority : Bool
open SudangrassBoundary public

canonicalSudangrassBoundary : SudangrassBoundary
canonicalSudangrassBoundary = sudangrass-boundary
  false false false false false true true true false

attributionRule : String
attributionRule =
  "Kaneko et al. 2023 owns its brachiariagrass-establishment companion-crop observations; Guretzky & Redfearn 2021 owns its Nebraska sorghum-sudangrass seeding-rate/forage/next-year vegetation observations; Burt et al. 2025 owns its agricultural forage-mixture/weed-suppression observations. DASHI owns only the temporary-nurse/reversibility and no-promotion boundaries. Sorghum-sudangrass is not identified with native restoration vegetation."
