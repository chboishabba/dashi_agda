module DASHI.Biology.Agriculture.CoverCropNitrogenCarryoverCounterfactualExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Biology.Agriculture.SudangrassNurseCoverCropExact as Sudangrass
import DASHI.Biology.Agriculture.NitrogenaseChemistryCrossPollinationExact as Chemistry

------------------------------------------------------------------------
-- AGRICULTURAL COVER-CROP N CARRYOVER / FERTILIZER COUNTERFACTUAL COMPARATOR
--
-- This owner supplies an external experimental-shape comparator for the open
-- Acacia/Senegalia terminal BNF stages.  It does NOT promote annual-cover-crop
-- fertilizer-replacement values to Acacia or mutate the canonical ladder.
------------------------------------------------------------------------

fontesEtAl2017DOI : String
fontesEtAl2017DOI = "10.2134/agronj2017.03.0180"

besanconEtAl2021DOI : String
besanconEtAl2021DOI = "10.21273/HORTTECH04811-21"

dorissantEtAl2022DOI : String
dorissantEtAl2022DOI = "10.1002/agg2.20311"

fontesEtAl2017 : Attribution.AttributedSource
fontesEtAl2017 = Attribution.mkDOISource
  "Giovani Preza Fontes; Peter J. Tomlinson; Ignacio A. Ciampitti; Charles W. Rice"
  "Grain Sorghum Response to Nitrogen Fertilizer following Cover Crops"
  "Agronomy Journal 109(6):2723-2737"
  "2017" fontesEtAl2017DOI "https://doi.org/10.2134/agronj2017.03.0180"
  Attribution.academicArticleSource
  "Field cropping-system study crossing cover-crop predecessor identity with five mineral-N rates (0, 45, 90, 135, 180 kg N ha-1) applied to grain sorghum, with grain yield and total N uptake measured. Late-maturing soybean increased sorghum yield at suboptimal N and was assigned a 44 kg N ha-1 fertilizer-replacement value in the source system; sorghum-sudangrass preceding sorghum remained N-limited and required added N to maintain yield. Retained as an explicit counterfactual-shape comparator, not an Acacia fertilizer-replacement result."
  Attribution.publicAttribution

besanconEtAl2021 : Attribution.AttributedSource
besanconEtAl2021 = Attribution.mkDOISource
  "Thierry E. Besancon; Maggie H. Wasacz; Joseph R. Heckman"
  "Weed Suppression, Nitrogen Availability, and Cabbage Production Following Sunn Hemp or Sorghum-sudangrass"
  "HortTechnology 31(4):439-447"
  "2021" besanconEtAl2021DOI "https://doi.org/10.21273/HORTTECH04811-21"
  Attribution.academicArticleSource
  "Two-year field study comparing sunn-hemp and sorghum-sudangrass predecessor effects on subsequent cabbage-season soil N, weeds and commercial yield. Despite the legume/nonlegume contrast, there was little evidence of a functional difference in soil N availability for the following cabbage crop; heavy rainfall was identified as a plausible loss pathway. Weed suppression and N carryover therefore remain separate consumers."
  Attribution.publicAttribution

dorissantEtAl2022 : Attribution.AttributedSource
dorissantEtAl2022 = Attribution.mkDOISource
  "Larousse Dorissant; Zachary T. Brym; Stacy Swartz"
  "Residue decomposition dynamics in mixed ratios of two warm-season cover crops"
  "Agrosystems, Geosciences & Environment 5:e20311"
  "2022" dorissantEtAl2022DOI "https://doi.org/10.1002/agg2.20311"
  Attribution.academicArticleSource
  "Humid-subtropical field decomposition experiment using sunn-hemp and sorghum-sudangrass residues at multiple mixture ratios over 56 days. Increasing sunn-hemp fraction increased early N release, but rapid decomposition and possible nutrient loss mean residue-N release is not identified with subsequent-crop N capture. Timing, residue ratio and retention context remain explicit."
  Attribution.publicAttribution

data CarryoverEvidenceRole : Set where
  predecessorNitrogenResponseCurve : CarryoverEvidenceRole
  residueNitrogenRelease : CarryoverEvidenceRole
  followingCropNitrogenAvailability : CarryoverEvidenceRole
  fertilizerReplacementValue : CarryoverEvidenceRole
  weedSuppressionCarryover : CarryoverEvidenceRole

data CounterfactualCoordinate : Set where
  predecessorIdentity : CounterfactualCoordinate
  mineralNitrogenRate : CounterfactualCoordinate
  followingCropIdentity : CounterfactualCoordinate
  cropNitrogenUptake : CounterfactualCoordinate
  cropYield : CounterfactualCoordinate
  residueReleaseTiming : CounterfactualCoordinate
  rainfallOrLeachingContext : CounterfactualCoordinate
  soilRetentionContext : CounterfactualCoordinate

record CarryoverReceipt : Set where
  constructor carryover-receipt
  field
    source : Attribution.AttributedSource
    sourceDOI : String
    role : CarryoverEvidenceRole
    cropReading : String
    nitrogenReading : String
    boundedReading : String
open CarryoverReceipt public

explicitNRateCounterfactualReceipt : CarryoverReceipt
explicitNRateCounterfactualReceipt = carryover-receipt
  fontesEtAl2017 fontesEtAl2017DOI fertilizerReplacementValue
  "grain sorghum following multiple cover-crop/fallow predecessors"
  "five explicit mineral-N rates plus grain yield and total crop-N uptake; system-specific replacement value estimated for late-maturing soybean"
  "quantification depends on the crop, predecessor, N-rate response, site and management; the result is not transported to Acacia/Senegalia"

followingCropAvailabilityReceipt : CarryoverReceipt
followingCropAvailabilityReceipt = carryover-receipt
  besanconEtAl2021 besanconEtAl2021DOI followingCropNitrogenAvailability
  "late-summer cabbage following sunn hemp or sorghum-sudangrass"
  "little functional predecessor difference in measured soil-N availability despite legume/nonlegume identity; rainfall loss context retained"
  "legume predecessor identity alone does not identify following-crop N availability or yield benefit"

residueReleaseReceipt : CarryoverReceipt
residueReleaseReceipt = carryover-receipt
  dorissantEtAl2022 dorissantEtAl2022DOI residueNitrogenRelease
  "surface residues of sunn hemp / sorghum-sudangrass mixtures"
  "early N release increases with sunn-hemp fraction, while rapid decomposition can temporally decouple release from subsequent crop uptake"
  "residue chemistry is a source-term observation, not a measured crop-demand or fertilizer-substitution receipt"

------------------------------------------------------------------------
-- Canonical nitrogenase ladder remains authoritative.
------------------------------------------------------------------------

genericSeasonalDemandStillOpen :
  Chemistry.stageClosed Chemistry.seasonalCropNDemand ≡ false
genericSeasonalDemandStillOpen = refl

genericAvoidedMineralNStillOpen :
  Chemistry.stageClosed Chemistry.avoidedMineralN ≡ false
genericAvoidedMineralNStillOpen = refl

sudangrassBoundaryReused : Sudangrass.SudangrassBoundary
sudangrassBoundaryReused = Sudangrass.canonicalSudangrassBoundary

------------------------------------------------------------------------
-- Exact evidence-shape contract for a quantified fertilizer replacement.
------------------------------------------------------------------------

record FertilizerReplacementEvidenceShape : Set where
  constructor fertilizer-replacement-evidence-shape
  field
    predecessorOrBNFStateObserved : Bool
    explicitMineralNRateCounterfactual : Bool
    followingCropIdentityRetained : Bool
    cropYieldObserved : Bool
    cropNitrogenUptakeObserved : Bool
    temporalAlignmentRetained : Bool
    soilAndLossContextRetained : Bool
    sourceIdentityRetained : Bool
open FertilizerReplacementEvidenceShape public

fontesComparatorShape : FertilizerReplacementEvidenceShape
fontesComparatorShape = fertilizer-replacement-evidence-shape
  true true true true true true true true

record CarryoverBoundary : Set where
  constructor carryover-boundary
  field
    residueNReleaseImpliesCropAvailableNAtDemandTime : Bool
    cropAvailableNImpliesCropNitrogenUptake : Bool
    cropNitrogenUptakeImpliesFertilizerReplacementValue : Bool
    legumePredecessorIdentityImpliesQuantifiedFertilizerReplacement : Bool
    sorghumSudangrassResidueNImpliesBiologicalNFixation : Bool
    explicitMineralNRateCounterfactualRequiredForReplacementValue : Bool
    cropYieldAndCropNUptakeMustRemainSeparate : Bool
    releaseTimingAndLossContextMustRemainIndexed : Bool
    quantifiedReplacementValueTransfersAcrossCropSystems : Bool
    annualCoverCropReplacementValueClosesAcaciaAvoidedMineralN : Bool
    annualCoverCropComparatorClosesAcaciaSeasonalDemand : Bool
    comparatorCreatesDeploymentAuthority : Bool
open CarryoverBoundary public

canonicalCarryoverBoundary : CarryoverBoundary
canonicalCarryoverBoundary = carryover-boundary
  false false false false false true true true false false false false

attributionRule : String
attributionRule =
  "Fontes et al. 2017 (DOI 10.2134/agronj2017.03.0180) owns its grain-sorghum predecessor-by-N-rate response, crop-N uptake and system-specific 44 kg N ha-1 late-maturing-soybean replacement-value propositions. Besancon, Wasacz & Heckman 2021 (DOI 10.21273/HORTTECH04811-21) owns its sunn-hemp/sorghum-sudangrass predecessor, following-cabbage soil-N, weed and yield observations. Dorissant, Brym & Swartz 2022 (DOI 10.1002/agg2.20311) owns its residue-mixture C/N decomposition observations. DASHI owns only the typed carryover chain, fertilizer-counterfactual evidence-shape contract and no-promotion boundary. The annual agricultural comparator does not create Acacia/Senegalia same-object evidence and does not close seasonalCropNDemand or avoidedMineralN in the canonical nitrogenase ladder."
