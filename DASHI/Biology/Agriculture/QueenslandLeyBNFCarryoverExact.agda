module DASHI.Biology.Agriculture.QueenslandLeyBNFCarryoverExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Biology.Agriculture.NitrogenaseChemistryCrossPollinationExact as Chemistry
import DASHI.Biology.Agriculture.CoverCropNitrogenCarryoverCounterfactualExact as Counterfactual
import DASHI.Biology.Agriculture.ConstructiveNitrogenTransportKernelExact as Transport

------------------------------------------------------------------------
-- QUEENSLAND LEY BNF -> N CARRYOVER -> FOLLOWING-CROP RESPONSE
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

dalalEtAl2004DurationDOI : String
dalalEtAl2004DurationDOI = "10.1071/EA03166"

hossainEtAl1995 : Attribution.AttributedSource
hossainEtAl1995 = Attribution.mkDOISource
  "Shahid A. Hossain; S. A. Waring; W. M. Strong; Ram C. Dalal; E. J. Weston"
  "Estimates of nitrogen fixations by legumes in alternate cropping systems at Warra, Queensland, using enriched-15N dilution and natural 15N abundance techniques"
  "Australian Journal of Agricultural Research 46(3):493-505"
  "1995" hossainEtAl1995DOI "https://doi.org/10.1071/AR9950493"
  Attribution.academicArticleSource
  "Long-term Warra Vertisol experiment measuring legume N fixation over two years with enriched-15N dilution and natural-abundance 15N. The enriched method gave the more reliable estimates in the source. These are isotope-derived plant/system fixation estimates, not direct bacterial nitrogenase flux and not a fertilizer-substitution receipt."
  Attribution.publicAttribution

hossainEtAl1996Soil : Attribution.AttributedSource
hossainEtAl1996Soil = Attribution.mkDOISource
  "Shahid A. Hossain; Ram C. Dalal; S. A. Waring; W. M. Strong; E. J. Weston"
  "Comparison of legume-based cropping systems at Warra, Queensland. I. Soil nitrogen and organic carbon accretion and potentially mineralisable nitrogen"
  "Australian Journal of Soil Research 34(2):273-287"
  "1996" hossainEtAl1996SoilDOI "https://doi.org/10.1071/SR9960273"
  Attribution.academicArticleSource
  "Warra follow-on soil study separating total-soil N/C accretion, residue/root N and potentially mineralisable N from measured legume fixation. Net N accumulation could exceed estimated fixation and deep-subsoil ammonium uptake may contribute, so soil-N accretion is not identified one-to-one with biological fixation."
  Attribution.publicAttribution

hossainEtAl1996Crop : Attribution.AttributedSource
hossainEtAl1996Crop = Attribution.mkDOISource
  "Shahid A. Hossain; W. M. Strong; S. A. Waring; Ram C. Dalal; E. J. Weston"
  "Comparison of legume-based cropping systems at Warra, Queensland. II. Mineral nitrogen accumulation and availability to the subsequent wheat crop"
  "Australian Journal of Soil Research 34(2):289-297"
  "1996" hossainEtAl1996CropDOI "https://doi.org/10.1071/SR9960289"
  Attribution.academicArticleSource
  "Warra follow-on crop study measuring mineral N during fallow, subsequent wheat N uptake, grain yield and protein after grass-legume, lucerne, medic, chickpea and continuous-wheat systems. Mineral-N increase, crop N uptake and yield response remain distinct consumers and vary with ley identity and season."
  Attribution.publicAttribution

puEtAl2001 : Attribution.AttributedSource
puEtAl2001 = Attribution.mkDOISource
  "G. Pu; W. M. Strong; P. G. Saffigna; J. Doughton"
  "Denitrification, leaching and immobilisation of applied 15N following legume and grass pastures in a semi-arid climate in Australia"
  "Nutrient Cycling in Agroecosystems 59:199-207"
  "2001" puEtAl2001DOI "https://doi.org/10.1023/A:1014462305825"
  Attribution.academicArticleSource
  "Four consecutive 15N mass-balance experiments over 18 months at three Roma-district Queensland sites following lucerne, snail medic and long-term Mitchell-grass/naturalised-medic pasture. Loss/deep displacement changed strongly with rainfall, with available carbon and nitrate also important. Retained as a loss/immobilisation receipt, not direct BNF or fertilizer replacement."
  Attribution.publicAttribution

peoplesEtAl2017 : Attribution.AttributedSource
peoplesEtAl2017 = Attribution.mkDOISource
  "Lindsay W. Bell; John Lawrence; Brian Johnson; Mark B. Peoples"
  "New ley legumes increase nitrogen fixation and availability and grain crop yields in subtropical cropping systems"
  "Crop and Pasture Science 68(1):11-26"
  "2017" peoplesEtAl2017DOI "https://doi.org/10.1071/CP16248"
  Attribution.academicArticleSource
  "Multi-season, four-location southern-Queensland forage-legume study comparing fixed-N inputs, soil mineral N before following cereal crops and crop responses. High starting soil mineral N suppressed N2 fixation; shoot-N removal often prevented a positive whole-system N balance; following-crop response was site/crop dependent."
  Attribution.publicAttribution

strongEtAl2006 : Attribution.AttributedSource
strongEtAl2006 = Attribution.mkDOISource
  "W. M. Strong; Ram C. Dalal; E. J. Weston; K. J. Lehane; J. E. Cooper; A. J. King; C. J. Holmes"
  "Sustaining productivity of a Vertosol at Warra, Queensland, with fertilisers, no-tillage or legumes. 9. Production and nitrogen benefits from mixed grass and legume pastures in rotation with wheat"
  "Australian Journal of Experimental Agriculture 46(3):375-385"
  "2006" strongEtAl2006DOI "https://doi.org/10.1071/EA05007"
  Attribution.academicArticleSource
  "Long-term Warra mixed grass-legume ley followed by wheat assays. In selected years pasture-following yield was similar to continuous wheat fertilised with 75 kg N ha-1, while grain protein showed a stronger response; low stored soil water limited many assay crops. Retained as a single-rate equivalence and water-limited-response receipt, not a replacement curve."
  Attribution.publicAttribution

dalalEtAl2004Duration : Attribution.AttributedSource
dalalEtAl2004Duration = Attribution.mkDOISource
  "Ram C. Dalal; E. J. Weston; W. M. Strong; M. E. Probert; K. J. Lehane; J. E. Cooper; A. J. King; C. J. Holmes"
  "Sustaining productivity of a Vertosol at Warra, Queensland, with fertilisers, no-tillage or legumes. 8. Effect of duration of lucerne ley on soil nitrogen and water, wheat yield and protein"
  "Australian Journal of Experimental Agriculture 44(10):1013-1024"
  "2004" dalalEtAl2004DurationDOI "https://doi.org/10.1071/EA03166"
  Attribution.academicArticleSource
  "Warra field experiment varying lucerne-ley duration from one to four years and jointly observing soil N increase, soil-water depletion/recovery, and subsequent wheat yield/protein. Longer lucerne duration increased lucerne N production and soil N to a point, while perennial lucerne created a soil-water deficit that could persist across seasons. Retained as a resource-tradeoff receipt: an N-service improvement is not a monotone following-crop benefit without water state and recovery time."
  Attribution.publicAttribution

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
  waterNitrogenResourceTradeoff : QueenslandLeyEvidenceRole

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
warraFixationReceipt = queensland-ley-receipt hossainEtAl1995 hossainEtAl1995DOI isotopeDerivedBNF
  "Warra, southern Queensland Vertisol" "two-year isotope observation inside a long-term experiment"
  "enriched-15N and natural-abundance estimates of fixed N" "legume-system fixed-N quantity"
  "method/treatment remain indexed; isotope-derived fixation is not direct bacterial flux or downstream crop capture"

warraSoilAccretionReceipt : QueenslandLeyReceipt
warraSoilAccretionReceipt = queensland-ley-receipt hossainEtAl1996Soil hossainEtAl1996SoilDOI soilNitrogenAccretion
  "Warra, southern Queensland Vertisol" "soil state after legume phases"
  "total soil N/C, residue/root N and potentially mineralisable N" "soil-N storage/mineralisation potential"
  "deep-subsoil N capture can contribute; soil-N accretion is not fixation one-to-one"

warraFollowingCropReceipt : QueenslandLeyReceipt
warraFollowingCropReceipt = queensland-ley-receipt hossainEtAl1996Crop hossainEtAl1996CropDOI followingCropNitrogenUptake
  "Warra, southern Queensland Vertisol" "fallow mineral-N observations followed by wheat"
  "profile mineral N, wheat N uptake, yield and protein" "following-crop capture and production response"
  "mineral N, crop N uptake and crop yield remain separate and season/system indexed"

romaLossReceipt : QueenslandLeyReceipt
romaLossReceipt = queensland-ley-receipt puEtAl2001 puEtAl2001DOI nitrogenLossOrImmobilisation
  "three Roma-district Queensland pasture sites" "four sequential 15N mass-balance periods over 18 months"
  "applied-15N recovery, loss, deep displacement and immobilisation context" "retention/loss pathway"
  "rainfall, available carbon, nitrate and profile geometry remain explicit; tracer fate is not equivalent to fixed-N fate"

southernQueenslandLeyReceipt : QueenslandLeyReceipt
southernQueenslandLeyReceipt = queensland-ley-receipt peoplesEtAl2017 peoplesEtAl2017DOI multiSiteLeyCarryover
  "four locations in southern Queensland" "multiple forage-legume seasons followed by cereals"
  "Ndfa/fixed-N, mineral N, shoot export and following cereal response" "multi-site carryover trajectory"
  "starting N suppresses fixation; export can erase positive balance; yield response is not universal"

warraSingleRateComparatorReceipt : QueenslandLeyReceipt
warraSingleRateComparatorReceipt = queensland-ley-receipt strongEtAl2006 strongEtAl2006DOI singleRateFertilizerEquivalence
  "Warra, southern Queensland Vertisol" "45-month mixed pasture followed by multiple wheat assay years"
  "pasture-following wheat versus unfertilised and 75 kg N ha-1 continuous-wheat comparators" "yield/protein response"
  "one-rate similarity does not identify an N response curve or replacement value; water limitation remains causal"

warraDurationTradeoffReceipt : QueenslandLeyReceipt
warraDurationTradeoffReceipt = queensland-ley-receipt dalalEtAl2004Duration dalalEtAl2004DurationDOI waterNitrogenResourceTradeoff
  "Warra, southern Queensland Vertisol" "one-, two-, three- and four-year lucerne leys followed by wheat"
  "lucerne N production and soil-N recovery observed jointly with soil-water depletion/recharge" "following wheat yield/protein under coupled N-water state"
  "longer ley duration is not a scalar improvement: N service and soil-water availability can move in opposing directions"

counterfactualShape : Counterfactual.FertilizerReplacementEvidenceShape
counterfactualShape = Counterfactual.fontesComparatorShape

data CarryoverStage : Set where
  biologicallyFixedN : CarryoverStage
  accumulatedSystemN : CarryoverStage
  mineralisedNAtSowing : CarryoverStage
  cropCapturedN : CarryoverStage
  cropProductionResponse : CarryoverStage
  avoidedMineralFertilizer : CarryoverStage

genericSeasonalDemandStillOpen : Chemistry.stageClosed Chemistry.seasonalCropNDemand ≡ false
genericSeasonalDemandStillOpen = refl

genericAvoidedMineralNStillOpen : Chemistry.stageClosed Chemistry.avoidedMineralN ≡ false
genericAvoidedMineralNStillOpen = refl

record QueenslandLeyBoundary : Set where
  constructor queensland-ley-boundary
  field
    fixedNitrogenQuantityImpliesSameMineralNitrogenAtCropSowing : Bool
    soilMineralNitrogenImpliesEquivalentCropNitrogenUptake : Bool
    cropNitrogenUptakeImpliesYieldBenefit : Bool
    fixedNitrogenInputImpliesAvoidedMineralFertilizer : Bool
    singleFertilizerRateYieldEquivalenceImpliesReplacementValue : Bool
    waterLimitationMayBeDroppedFromFollowingCropResponse : Bool
    soilNitrogenImprovementImpliesRecoveredSoilWater : Bool
    longerLeyDurationImpliesMonotoneFollowingCropBenefit : Bool
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
    constructiveTransportKernelMathOwned : Bool
    empiricalPolynomialGeometricKernelBoundOwned : Bool
    finiteObservationImpliesAsymptoticStabilisation : Bool
open QueenslandLeyBoundary public

canonicalQueenslandLeyBoundary : QueenslandLeyBoundary
canonicalQueenslandLeyBoundary = record
  { fixedNitrogenQuantityImpliesSameMineralNitrogenAtCropSowing = false
  ; soilMineralNitrogenImpliesEquivalentCropNitrogenUptake = false
  ; cropNitrogenUptakeImpliesYieldBenefit = false
  ; fixedNitrogenInputImpliesAvoidedMineralFertilizer = false
  ; singleFertilizerRateYieldEquivalenceImpliesReplacementValue = false
  ; waterLimitationMayBeDroppedFromFollowingCropResponse = false
  ; soilNitrogenImprovementImpliesRecoveredSoilWater = false
  ; longerLeyDurationImpliesMonotoneFollowingCropBenefit = false
  ; denitrificationLeachingImmobilisationMayBeDropped = false
  ; startingMineralNitrogenMayBeDroppedFromBNF = false
  ; cropIdentityAndSeasonMayBeDropped = false
  ; isotopeDerivedBNFEqualsDirectBacterialFlux = false
  ; soilNitrogenAccretionEqualsBiologicalFixation = false
  ; forageShootExportMayBeDroppedFromSystemBalance = false
  ; explicitMineralNRateCounterfactualRequiredForReplacement = true
  ; fixationSoilMineralNUptakeAndYieldRemainSeparateStages = true
  ; queenslandLeyEvidenceClosesAcaciaAvoidedMineralN = false
  ; queenslandLeyEvidenceCreatesAcaciaSameObjectReceipt = false
  ; queenslandLeyEvidenceCreatesDeploymentAuthority = false
  ; constructiveTransportKernelMathOwned = true
  ; empiricalPolynomialGeometricKernelBoundOwned = false
  ; finiteObservationImpliesAsymptoticStabilisation = false
  }

constructiveTransportMathReused : Transport.NitrogenTransportMathBoundary
constructiveTransportMathReused =
  Transport.canonicalNitrogenTransportMathBoundary

fixedNDoesNotIdentifySowingMineralN : fixedNitrogenQuantityImpliesSameMineralNitrogenAtCropSowing canonicalQueenslandLeyBoundary ≡ false
fixedNDoesNotIdentifySowingMineralN = refl

soilMineralNDoesNotIdentifyCropCapture : soilMineralNitrogenImpliesEquivalentCropNitrogenUptake canonicalQueenslandLeyBoundary ≡ false
soilMineralNDoesNotIdentifyCropCapture = refl

cropCaptureDoesNotIdentifyYield : cropNitrogenUptakeImpliesYieldBenefit canonicalQueenslandLeyBoundary ≡ false
cropCaptureDoesNotIdentifyYield = refl

fixedNDoesNotIdentifyReplacement : fixedNitrogenInputImpliesAvoidedMineralFertilizer canonicalQueenslandLeyBoundary ≡ false
fixedNDoesNotIdentifyReplacement = refl

singleRateComparatorDoesNotIdentifyReplacement : singleFertilizerRateYieldEquivalenceImpliesReplacementValue canonicalQueenslandLeyBoundary ≡ false
singleRateComparatorDoesNotIdentifyReplacement = refl

acaciaAvoidedMineralNStillOpen : queenslandLeyEvidenceClosesAcaciaAvoidedMineralN canonicalQueenslandLeyBoundary ≡ false
acaciaAvoidedMineralNStillOpen = refl

attributionRule : String
attributionRule =
  "Hossain et al. 1995 (DOI 10.1071/AR9950493) owns its Warra isotope-derived fixation estimates. Hossain et al. 1996-I (DOI 10.1071/SR9960273) owns its soil-N/C and potentially-mineralisable-N observations. Hossain et al. 1996-II (DOI 10.1071/SR9960289) owns its mineral-N, following-wheat N-uptake/yield/protein observations. Pu et al. 2001 (DOI 10.1023/A:1014462305825) owns its Roma 15N loss/displacement observations. Bell, Lawrence, Johnson & Peoples 2017 (DOI 10.1071/CP16248) owns its multi-site forage-legume fixation/mineral-N/following-crop observations. Strong et al. 2006 (DOI 10.1071/EA05007) owns its Warra mixed-pasture wheat comparison and stored-water limitation observations. Dalal et al. 2004 (DOI 10.1071/EA03166) owns its lucerne-duration × soil-N × soil-water × following-wheat observations. DASHI owns only the typed stage/resource separations, reuse of the generic constructive transport/convergence mathematics, and the no-promotion boundary. The imported convolution/tail theorems do not assert that any Queensland source follows a polynomial-geometric kernel; such a pointwise empirical majorant remains unpaid. These Queensland systems do not create Acacia/Senegalia same-object evidence, direct bacterial flux, quantified Acacia fertilizer substitution, or deployment authority."
