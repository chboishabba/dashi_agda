module DASHI.Biology.Agriculture.AustralianAcaciaGrassSoilNitrogenLegacyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Biology.Agriculture.NitrogenaseChemistryCrossPollinationExact as Chemistry

------------------------------------------------------------------------
-- AUSTRALIAN ACACIA <-> GRASS LAND-USE SOIL-N LEGACY
------------------------------------------------------------------------

allenEtAl2016DOI : String
allenEtAl2016DOI = "10.1071/RJ16009"

pringleEtAl2016DOI : String
pringleEtAl2016DOI = "10.1071/RJ16010"

thorntonShrestha2021DOI : String
thorntonShrestha2021DOI = "10.1071/SR20088"

kirschbaumEtAl2008DOI : String
kirschbaumEtAl2008DOI = "10.1016/j.soilbio.2007.09.003"

allenEtAl2016 : Attribution.AttributedSource
allenEtAl2016 = Attribution.mkDOISource
  "D. E. Allen; M. J. Pringle; D. W. Butler; B. K. Henry; T. F. A. Bishop; S. G. Bray; T. G. Orton; R. C. Dalal"
  "Effects of land-use change and management on soil carbon and nitrogen in the Brigalow Belt, Australia: I. Overview and inventory"
  "The Rangeland Journal 38(5):443-452"
  "2016"
  allenEtAl2016DOI
  "https://doi.org/10.1071/RJ16009"
  Attribution.academicArticleSource
  "Queensland Brigalow Belt inventory across 45 matched remnant-pasture-regrowth triplets, with regrowth ages spanning roughly 10-58 years. Soil total organic C, total N and stable isotopes retain land-use and history dependence; regrowth is not assumed to recreate every remnant soil pool."
  Attribution.publicAttribution

pringleEtAl2016 : Attribution.AttributedSource
pringleEtAl2016 = Attribution.mkDOISource
  "M. J. Pringle; D. E. Allen; T. G. Orton; T. F. A. Bishop; D. W. Butler; B. K. Henry; S. G. Bray; R. C. Dalal"
  "Effects of land-use change and management on soil carbon and nitrogen in the Brigalow Belt, Australia: II. Statistical models to unravel the climate-soil-management interaction"
  "The Rangeland Journal 38(5):453-466"
  "2016"
  pringleEtAl2016DOI
  "https://doi.org/10.1071/RJ16010"
  Attribution.academicArticleSource
  "Statistical analysis of the Brigalow Belt land-use inventory. Fire clearing reduced TOC and TN; pasture conversion altered delta-13C; subsequent native regrowth could restore the isotope signal without a corresponding restoration of TOC stock. Climate, soil P and management interactions remain explicit."
  Attribution.publicAttribution

thorntonShrestha2021 : Attribution.AttributedSource
thorntonShrestha2021 = Attribution.mkDOISource
  "Craig M. Thornton; Karuna Shrestha"
  "The Brigalow Catchment Study: V. Clearing and burning brigalow (Acacia harpophylla) in Queensland, Australia, temporarily increases surface soil fertility prior to nutrient decline under cropping or grazing"
  "Soil Research 59(2):146-169"
  "2021"
  thorntonShrestha2021DOI
  "https://doi.org/10.1071/SR20088"
  Attribution.academicArticleSource
  "Long-running Queensland catchment experiment initiated in 1965. Clearing/burning caused a short-lived surface-fertility pulse through heating/ash, followed by multi-decadal nutrient decline under cropping or grazing; total N declined strongly in cleared land uses. The initial positive pulse is therefore not a persistent fertility state."
  Attribution.publicAttribution

kirschbaumEtAl2008 : Attribution.AttributedSource
kirschbaumEtAl2008 = Attribution.mkDOISource
  "Miko U. F. Kirschbaum; Ben Harms; Nicole J. Mathers; Ram C. Dalal"
  "Soil carbon and nitrogen changes after clearing mulga (Acacia aneura) vegetation in Queensland, Australia: Observations, simulations and scenario analysis"
  "Soil Biology and Biochemistry 40(2):392-405"
  "2008"
  kirschbaumEtAl2008DOI
  "https://doi.org/10.1016/j.soilbio.2007.09.003"
  Attribution.academicArticleSource
  "Queensland Mulga-to-buffel-grass land-use transition combining field observations with CenW modelling. After removal of the N-fixing woody overstorey and maintenance as non-legume buffel pasture, soil organic C and N stocks continued to decline. Model reproduction is retained separately from direct measurement."
  Attribution.publicAttribution

data AcaciaGrassSoilEvidenceRole : Set where
  matchedRemnantPastureRegrowthInventory : AcaciaGrassSoilEvidenceRole
  managementClimateSoilInteraction : AcaciaGrassSoilEvidenceRole
  clearingBurningLongTermNutrientTrajectory : AcaciaGrassSoilEvidenceRole
  mulgaBuffelCarbonNitrogenTransition : AcaciaGrassSoilEvidenceRole

record AcaciaGrassSoilReceipt : Set where
  constructor acacia-grass-soil-receipt
  field
    source : Attribution.AttributedSource
    sourceDOI : String
    role : AcaciaGrassSoilEvidenceRole
    vegetationReading : String
    timeReading : String
    soilReading : String
    boundedReading : String
open AcaciaGrassSoilReceipt public

brigalowInventoryReceipt : AcaciaGrassSoilReceipt
brigalowInventoryReceipt = acacia-grass-soil-receipt
  allenEtAl2016 allenEtAl2016DOI matchedRemnantPastureRegrowthInventory
  "remnant Acacia harpophylla, pasture after clearing, and spontaneous brigalow regrowth"
  "regrowth age 10-58 years in a matched-site design"
  "TOC, TN, stable-isotope and management coordinates"
  "current vegetation class is not identified with complete soil-state recovery"

brigalowInteractionReceipt : AcaciaGrassSoilReceipt
brigalowInteractionReceipt = acacia-grass-soil-receipt
  pringleEtAl2016 pringleEtAl2016DOI managementClimateSoilInteraction
  "Brigalow Belt land uses with native regrowth among pasture"
  "land-use history plus time since clearing"
  "TOC, TN, POC, delta-13C, delta-15N; climate/P/management interactions"
  "delta-13C return toward native state can occur without TOC-stock recovery"

catchmentNutrientTrajectoryReceipt : AcaciaGrassSoilReceipt
catchmentNutrientTrajectoryReceipt = acacia-grass-soil-receipt
  thorntonShrestha2021 thorntonShrestha2021DOI clearingBurningLongTermNutrientTrajectory
  "intact brigalow versus cleared/cropped or cleared/grazed catchments"
  "initial burn pulse followed across decades"
  "surface mineral/total nutrient trajectories including TN"
  "initial ash-bed fertility pulse and sustained soil fertility are different temporal states"

mulgaBuffelTransitionReceipt : AcaciaGrassSoilReceipt
mulgaBuffelTransitionReceipt = acacia-grass-soil-receipt
  kirschbaumEtAl2008 kirschbaumEtAl2008DOI mulgaBuffelCarbonNitrogenTransition
  "N-fixing Acacia aneura woodland converted to non-legume buffel-grass pasture"
  "post-clearing observations plus simulation scenarios"
  "soil C/N stocks and N mineralisation with depth"
  "continued C/N decline is observed; model fit does not become a direct BNF-flux measurement"

------------------------------------------------------------------------
-- Canonical BNF ladder is not inferred from land-cover signatures.
------------------------------------------------------------------------

bacterialFixedNFluxStillOpen :
  Chemistry.stageClosed Chemistry.bacterialFixedNFlux ≡ false
bacterialFixedNFluxStillOpen = refl

record AcaciaGrassSoilBoundary : Set where
  constructor acacia-grass-soil-boundary
  field
    initialPostClearingFertilityPulseImpliesSustainedFertility : Bool
    regrowthVegetationSignalImpliesRecoveredSoilCarbonNitrogen : Bool
    recoveredDelta13CImpliesRecoveredTotalOrganicCarbon : Bool
    acaciaLandCoverImpliesMeasuredBiologicalNitrogenFixationFlux : Bool
    buffelPastureImpliesSameNitrogenInputRegimeAsAcaciaWoodland : Bool
    clearingFireCroppingGrazingHistoryMayBeDropped : Bool
    soilPhosphorusAndClimateMayBeDropped : Bool
    modelReproductionCreatesDirectFluxMeasurement : Bool
    decliningSoilNQuantifiesLostBNFFlux : Bool
    landUseContrastCreatesFertilizerSubstitutionReceipt : Bool
open AcaciaGrassSoilBoundary public

canonicalAcaciaGrassSoilBoundary : AcaciaGrassSoilBoundary
canonicalAcaciaGrassSoilBoundary = acacia-grass-soil-boundary
  false false false false false false false false false false

attributionRule : String
attributionRule =
  "Allen et al. 2016 (DOI 10.1071/RJ16009) owns its matched Brigalow remnant/pasture/regrowth soil C-N inventory propositions. Pringle et al. 2016 (DOI 10.1071/RJ16010) owns its climate-soil-management statistical propositions, including the delta-13C/TOC divergence. Thornton & Shrestha 2021 (DOI 10.1071/SR20088) owns the Brigalow Catchment Study clearing/burning fertility-pulse and long-term nutrient-decline propositions. Kirschbaum et al. 2008 (DOI 10.1016/j.soilbio.2007.09.003) owns its Mulga-to-buffel observations and CenW scenario/model propositions. DASHI owns only the temporal/state separations and no-promotion boundary. Land-cover, soil-isotope and soil-stock contrasts are not relabelled as measured BNF flux, lost fixation quantity, crop-demand satisfaction or fertilizer substitution."
