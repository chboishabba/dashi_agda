module DASHI.Biology.Agriculture.QueenslandLeyBNFCarryoverExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Biology.Agriculture.NitrogenaseChemistryCrossPollinationExact as Chemistry
import DASHI.Biology.Agriculture.CoverCropNitrogenCarryoverCounterfactualExact as Counterfactual

------------------------------------------------------------------------
-- QUEENSLAND LEY BNF -> N CARRYOVER -> FOLLOWING-CROP RESPONSE
--
-- This owner preserves a same-region experimental chain across Warra, Roma
-- and later southern-Queensland ley work.  It distinguishes isotope-derived
-- legume N fixation, soil/organic-N accretion, mineral-N availability at the
-- following crop, crop N uptake, crop yield, and N loss/immobilisation.
--
-- It is a positive evidence-shape comparator for the open Acacia/Senegalia
-- terminal BNF stages.  It does NOT transfer Queensland ley values to Acacia
-- and does NOT close the canonical seasonalCropNDemand/avoidedMineralN debt.
------------------------------------------------------------------------

hossainEtAl1995DOI : String
hossainEtAl1995DOI = "10.1071/AR9950493"

hossainEtAl1996SoilDOI : String
hossainEtAl1996SoilDOI = "10.1071/SR9960273"

hossainEtAl1996CropDOI : String
hossainEtAl1996CropDOI = "10.1071/SR9960289"

puEtAl2001DOI : String
puEtAl2001DOI = "10.1023/A:1014462305825"

peoplesEtAl2017DOI : String
peoplesEtAl2017DOI = "10.1071/CP16248"

strongEtAl2006DOI : String
strongEtAl2006DOI = "10.1071/EA05007"

hossainEtAl1995 : Attribution.AttributedSource
hossainEtAl1995 = Attribution.mkDOISource
  "Shahid A. Hossain; S. A. Waring; W. M. Strong; Ram C. Dalal; E. J. Weston"
  "Estimates of nitrogen fixations by legumes in alternate cropping systems at Warra, Queensland, using enriched-15N dilution and natural 15N abundance techniques"
  "Australian Journal of Agricultural Research 46(3):493-505"
  "1995"
  hossainEtAl1995DOI
  "https://doi.org/10.1071/AR9950493"
  Attribution.academicArticleSource
  "Long-term Warra Vertisol experiment measuring legume N fixation over two years with enriched-15N dilution and natural-abundance 15N. The enriched method gave the more reliable estimates in the source. Grass-legume, lucerne, medic and chickpea systems differ in fixation quantity and method response. These are isotope-derived plant/system fixation estimates, not direct bacterial nitrogenase flux and not a fertilizer-substitution receipt."
  Attribution.publicAttribution

hossainEtAl1996Soil : Attribution.AttributedSource
hossainEtAl1996Soil = Attribution.mkDOISource
  "Shahid A. Hossain; Ram C. Dalal; S. A. Waring; W. M. Strong; E. J. Weston"
  "Comparison of legume-based cropping systems at Warra, Queensland. I. Soil nitrogen and organic carbon accretion and potentially mineralisable nitrogen"
  "Australian Journal of Soil Research 34(2):273-287"
  "1996"
  hossainEtAl1996SoilDOI
  "https://doi.org/10.1071/SR9960273"
  Attribution.academicArticleSource
  "Warra follow-on soil study separating total-soil N/C accretion, residue/root N and potentially mineralisable N from measured legume fixation. The source notes that net N accumulation could exceed estimated fixation and that deep-subsoil ammonium uptake may contribute, so soil-N accretion is not identified one-to-one with biological fixation."
  Attribution.publicAttribution

hossainEtAl1996Crop : Attribution.AttributedSource
hossainEtAl1996Crop = Attribution.mkDOISource
  "Shahid A. Hossain; W. M. Strong; S. A. Waring; Ram C. Dalal; E. J. Weston"
  "Comparison of legume-based cropping systems at Warra, Queensland. II. Mineral nitrogen accumulation and availability to the subsequent wheat crop"
  "Australian Journal of Soil Research 34(2):289-297"
  "1996"
  hossainEtAl1996CropDOI
  "https://doi.org/10.1071/SR9960289"
  Attribution.academicArticleSource
  "Warra follow-on crop study measuring mineral N during fallow, subsequent wheat N uptake, grain yield and protein after grass-legume, lucerne, medic, chickpea and continuous-wheat systems. Mineral-N increase, crop N uptake and yield response are retained as distinct consumers and remain season/system dependent."
  Attribution.publicAttribution

puEtAl2001 : Attribution.AttributedSource
puEtAl2001 = Attribution.mkDOISource
  "G. Pu; W. M. Strong; P. G. Saffigna; J. Doughton"
  "Denitrification, leaching and immobilisation of applied 15N following legume and grass pastures in a semi-arid climate in Australia"
  "Nutrient Cycling in Agroecosystems 59:199-207"
  "2001"
  puEtAl2001DOI
  "https://doi.org/10.1023/A:1014462305825"
  Attribution.academicArticleSource
  "Four consecutive 15N mass-balance experiments over 18 months at three Roma-district Queensland sites following lucerne, snail medic and long-term Mitchell-grass/naturalised-medic pasture. Denitrification/loss and deep displacement changed strongly with rainfall, while available carbon and nitrate also mattered. Retained as a loss/immobilisation-pathway receipt, not as direct measurement of legume BNF or fertilizer replacement."
  Attribution.publicAttribution

peoplesEtAl2017 : Attribution.AttributedSource
peoplesEtAl2017 = Attribution.mkDOISource
  "Lindsay W. Bell; John Lawrence; Brian Johnson; Mark B. Peoples"
  "New ley legumes increase nitrogen fixation and availability and grain crop yields in subtropical cropping systems"
  "Crop and Pasture Science 68(1):11-26"
  "2017"
  peoplesEtAl2017DOI
  "https://doi.org/10.1071/CP16248"
  Attribution.academicArticleSource
  "Multi-season, four-location southern-Queensland forage-legume study comparing fixed-N inputs, soil mineral N before following cereal crops and subsequent crop responses. High starting soil mineral N suppressed N2 fixation; shoot-N removal often prevented a positive whole-system N balance; legume effects on following grain yield were site/crop dependent. The source therefore links multiple stages but does not supply a universal fertilizer-replacement value."
  Attribution.publicAttribution

strongEtAl2006 : Attribution.AttributedSource
strongEtAl2006 = Attribution.mkDOISource
  "W. M. Strong; Ram C. Dalal; E. J. Weston; K. J. Lehane; J. E. Cooper; A. J. King; C. J. Holmes"
  "Sustaining productivity of a Vertosol at Warra, Queensland, with fertilisers, no-tillage or legumes. 9. Production and nitrogen benefits from mixed grass and legume pastures in rotation with wheat"
  "Australian Journal of Experimental Agriculture 46(3):375-385"
  "2006"
  strongEtAl2006DOI
  "https://doi.org/10.1071/EA05007"
  Attribution.academicArticleSource
  "Long-term Warra mixed grass-legume ley followed by wheat assays. In most following wheat crops, yield was similar to unfertilised continuous wheat; in selected years pasture-following yield was similar to continuous wheat fertilised with 75 kg N ha-1, while grain protein showed a stronger response. Stored soil water was low enough to limit many assay crops. Retained as a single-rate equivalence and water-limited-response receipt, not a quantified fertilizer-replacement curve."
  Attribution.publicAttribution

------------------------------------------------------------------------
-- Evidence roles and receipts.
------------------------------------------------------------------------

data QueenslandLeyEvidenceRole : Set where
  isotopeDerivedBNF : QueenslandLeyEvidenceRole
  soilNitrogenAccretion : QueenslandLeyEvidenceRole
  potentiallyMineralisableNitrogen : QueenslandLeyEvidenceRole
  mineralNitrogenAtCropSowing : QueenslandLeyEvidenceRole
  followingCropNitrogenUptake : QueenslandLeyEvidenceRole
  followingCropYield : QueenslandLeyEvidenceRole
  nitrogenLossOrImmobilisation : QueenslandLeyEvidenceRole
  multiSiteLeyCarryover : QueenslandLeyEvidenceRole
  singleRateFertilizerEquivalence : QueenslandLeyEvidenceRole
  waterLimitedCropAssay : QueenslandLeyEvidenceRole

record QueenslandLeyReceipt : Set where
  constructor queensland-ley-receipt
  field
    source : Attribution.AttributedSource
    sourceDOI : String
    role : QueenslandLeyEvidenceRole
    locationReading : String
    temporalReading : String
    nitrogenReading : String
    consumerReading : String
    boundedReading : String
open QueenslandLeyReceipt public

warraFixationReceipt : QueenslandLeyReceipt
warraFixationReceipt = queensland-ley-receipt
  hossainEtAl1995 hossainEtAl1995DOI isotopeDerivedBNF
  "Warra, southern Queensland Vertisol"
  "two-year isotope observation inside a long-term alternate-cropping experiment"
  "enriched-15N dilution and natural-abundance 15N estimates of N derived from atmosphere / fixed N"
  "legume-system fixed-N quantity"
  "method and treatment remain indexed; isotope-derived fixation estimate is not direct bacterial flux and does not identify downstream crop capture"

warraSoilAccretionReceipt : QueenslandLeyReceipt
warraSoilAccretionReceipt = queensland-ley-receipt
  hossainEtAl1996Soil hossainEtAl1996SoilDOI soilNitrogenAccretion
  "Warra, southern Queensland Vertisol"
  "soil state after legume phases in the long-term experiment"
  "total soil N/C, residue/root N and potentially mineralisable N"
  "soil-N storage/mineralisation potential"
  "net soil-N accretion can include deep-subsoil N capture and therefore is not identified one-to-one with atmospheric fixation"

warraFollowingCropReceipt : QueenslandLeyReceipt
warraFollowingCropReceipt = queensland-ley-receipt
  hossainEtAl1996Crop hossainEtAl1996CropDOI followingCropNitrogenUptake
  "Warra, southern Queensland Vertisol"
  "fallow mineral-N observations followed by 1989/1990 wheat crops"
  "profile mineral N, wheat N uptake, grain yield and grain protein"
  "following-crop capture and production response"
  "mineral N, crop N uptake and crop yield are observed separately and vary with ley identity and season"

romaLossReceipt : QueenslandLeyReceipt
romaLossReceipt = queensland-ley-receipt
  puEtAl2001 puEtAl2001DOI nitrogenLossOrImmobilisation
  "three Roma-district Queensland pasture sites"
  "four sequential 15N mass-balance periods over 18 months"
  "applied-15N recovery, denitrification/loss, deep displacement and immobilisation context"
  "retention/loss pathway between N supply and later crop availability"
  "rainfall, available carbon, nitrate state and soil profile geometry remain explicit; applied tracer fate is not equivalent to biologically fixed-N fate"

southernQueenslandLeyReceipt : QueenslandLeyReceipt
southernQueenslandLeyReceipt = queensland-ley-receipt
  peoplesEtAl2017 peoplesEtAl2017DOI multiSiteLeyCarryover
  "four locations in southern Queensland"
  "multiple forage-legume seasons followed by cereal crops"
  "legume Ndfa/fixed-N inputs, soil mineral N before following crop, shoot-N removal and following cereal responses"
  "multi-site carryover trajectory"
  "high starting soil mineral N suppresses fixation; removed forage N can erase positive system balance; yield response is not universal across site/crop combinations"

warraSingleRateComparatorReceipt : QueenslandLeyReceipt
warraSingleRateComparatorReceipt = queensland-ley-receipt
  strongEtAl2006 strongEtAl2006DOI singleRateFertilizerEquivalence
  "Warra, southern Queensland fertility-depleted Vertosol"
  "45-month mixed pasture followed by multiple wheat assay years"
  "pasture-following wheat compared with unfertilised and 75 kg N ha-1 continuous-wheat comparators"
  "yield/protein response under low stored-water conditions"
  "similarity to one fertilizer rate in selected years does not identify a response curve or replacement value; water limitation remains an interacting cause"

------------------------------------------------------------------------
-- Cross-pollination with the explicit fertilizer-counterfactual template.
------------------------------------------------------------------------

counterfactualShape : Counterfactual.FertilizerReplacementEvidenceShape
counterfactualShape = Counterfactual.fontesComparatorShape

data CarryoverStage : Set where
  biologicallyFixedN : CarryoverStage
  accumulatedSystemN : CarryoverStage
  mineralisedNAtSowing : CarryoverStage
  cropCapturedN : CarryoverStage
  cropProductionResponse : CarryoverStage
  avoidedMineralFertilizer : CarryoverStage

------------------------------------------------------------------------
-- Canonical nitrogenase ladder remains authoritative.
------------------------------------------------------------------------

genericSeasonalDemandStillOpen :
  Chemistry.stageClosed Chemistry.seasonalCropNDemand ≡ false
genericSeasonalDemandStillOpen = refl

genericAvoidedMineralNStillOpen :
  Chemistry.stageClosed Chemistry.avoidedMineralN ≡ false
genericAvoidedMineralNStillOpen = refl

------------------------------------------------------------------------
-- No-promotion boundary.
------------------------------------------------------------------------

record QueenslandLeyBoundary : Set where
  constructor queensland-ley-boundary
  field
    fixedNitrogenQuantityImpliesSameMineralNitrogenAtCropSowing : Bool
    soilMineralNitrogenImpliesEquivalentCropNitrogenUptake : Bool
    cropNitrogenUptakeImpliesYieldBenefit : Bool
    fixedNitrogenInputImpliesAvoidedMineralFertilizer : Bool
    singleFertilizerRateYieldEquivalenceImpliesReplacementValue : Bool
    waterLimitationMayBeDroppedFromFollowingCropResponse : Bool
    denitrificationLeachingImmobilisationMayBeDropped : Bool
    startingMineralNitrogenMayBeDroppedFromBNF : Bool
    cropIdentityAndSeasonMayBeDropped : Bool
    isotopeDerivedBNFEqualsDirectBacterialFlux : Bool
    soilNitrogenAccretionEqualsBiologicalFixation : Bool
    forageShootExportMayBeDroppedFromSystemBalance : Bool
    explicitMineralNRateCounterfactualRequiredForReplacement : Bool
    fixationSoilMineralNUptakeAndYieldRemainSeparateStages : Bool
    queenslandLeyEvidenceClosesAcaciaAvoidedMineralN : Bool
    queenslandLeyEvidenceCreatesAcaciaSameObjectReceipt : Bool
    queenslandLeyEvidenceCreatesDeploymentAuthority : Bool
open QueenslandLeyBoundary public

canonicalQueenslandLeyBoundary : QueenslandLeyBoundary
canonicalQueenslandLeyBoundary = queensland-ley-boundary
  false false false false false false false false false false false false
  true true false false false

fixedNDoesNotIdentifySowingMineralN :
  fixedNitrogenQuantityImpliesSameMineralNitrogenAtCropSowing canonicalQueenslandLeyBoundary ≡ false
fixedNDoesNotIdentifySowingMineralN = refl

soilMineralNDoesNotIdentifyCropCapture :
  soilMineralNitrogenImpliesEquivalentCropNitrogenUptake canonicalQueenslandLeyBoundary ≡ false
soilMineralNDoesNotIdentifyCropCapture = refl

cropCaptureDoesNotIdentifyYield :
  cropNitrogenUptakeImpliesYieldBenefit canonicalQueenslandLeyBoundary ≡ false
cropCaptureDoesNotIdentifyYield = refl

fixedNDoesNotIdentifyReplacement :
  fixedNitrogenInputImpliesAvoidedMineralFertilizer canonicalQueenslandLeyBoundary ≡ false
fixedNDoesNotIdentifyReplacement = refl

singleRateComparatorDoesNotIdentifyReplacement :
  singleFertilizerRateYieldEquivalenceImpliesReplacementValue canonicalQueenslandLeyBoundary ≡ false
singleRateComparatorDoesNotIdentifyReplacement = refl

acaciaAvoidedMineralNStillOpen :
  queenslandLeyEvidenceClosesAcaciaAvoidedMineralN canonicalQueenslandLeyBoundary ≡ false
acaciaAvoidedMineralNStillOpen = refl

attributionRule : String
attributionRule =
  "Hossain, Waring, Strong, Dalal & Weston 1995 (DOI 10.1071/AR9950493) owns its Warra enriched-15N/natural-abundance estimates of legume-system N fixation. Hossain, Dalal, Waring, Strong & Weston 1996-I (DOI 10.1071/SR9960273) owns its soil-N/C accretion, residue/root-N and potentially-mineralisable-N observations. Hossain, Strong, Waring, Dalal & Weston 1996-II (DOI 10.1071/SR9960289) owns its fallow mineral-N, following-wheat N-uptake, grain-yield and protein observations. Pu, Strong, Saffigna & Doughton 2001 (DOI 10.1023/A:1014462305825) owns its Roma applied-15N loss/displacement/immobilisation mass-balance propositions. Bell, Lawrence, Johnson & Peoples 2017 (DOI 10.1071/CP16248) owns its multi-site southern-Queensland forage-legume fixation, soil-mineral-N and following-cereal response observations. Strong et al. 2006 (DOI 10.1071/EA05007) owns its Warra mixed-pasture following-wheat yield/protein comparison with unfertilised and 75 kg N ha-1 continuous-wheat comparators and its low stored-water limitation observation. DASHI owns only the typed carryover-stage separation and no-promotion boundary. These Queensland agricultural systems are methodological/causal comparators and do not create Acacia/Senegalia same-object evidence, direct bacterial flux, quantified Acacia fertilizer substitution, or deployment authority."
