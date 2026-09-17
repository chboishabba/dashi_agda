module DASHI.Biology.Agriculture.AcaciaSenegalFixedNTransferNutrientBudgetExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Biology.Agriculture.AcaciaSenegalPlantNitrogenAssimilationEvidenceExact as PlantN
import DASHI.Biology.Agriculture.AcaciaSenegalBNFMeasurementHierarchyExact as Measurement
import DASHI.Biology.Agriculture.NitrogenaseChemistryCrossPollinationExact as Chemistry

------------------------------------------------------------------------
-- ACACIA FIXED-N TRANSFER -> FIELD NUTRIENT-BUDGET BRIDGE
------------------------------------------------------------------------

isaacHinsingerHarmand2012DOI : String
isaacHinsingerHarmand2012DOI = "10.1016/j.scitotenv.2011.12.071"

isaacHinsingerHarmand2012PMID : String
isaacHinsingerHarmand2012PMID = "22446108"

raddadEtAl2006DOI : String
raddadEtAl2006DOI = "10.1007/s10457-006-9009-6"

deansEtAl1999DOI : String
deansEtAl1999DOI = "10.1016/S0378-1127(99)00063-8"

fallEtAl2012DOI : String
fallEtAl2012DOI = "10.1016/j.jenvman.2011.03.038"

fallEtAl2012PMID : String
fallEtAl2012PMID = "21514716"

elTahirEtAl2009DOI : String
elTahirEtAl2009DOI = "10.1016/j.jaridenv.2008.11.007"

basgaEtAl2018DOI : String
basgaEtAl2018DOI = "10.5897/AJAR2018.13283"

isaacHinsingerHarmand2012 : Attribution.AttributedSource
isaacHinsingerHarmand2012 = Attribution.mkDOISource
  "Marney E. Isaac; Philippe Hinsinger; Jean-Michel Harmand"
  "Nitrogen and phosphorus economy of a legume tree-cereal intercropping system under controlled conditions"
  "Science of the Total Environment 434:71-78"
  "2012"
  isaacHinsingerHarmand2012DOI
  "https://doi.org/10.1016/j.scitotenv.2011.12.071"
  Attribution.academicArticleSource
  "Controlled Acacia senegal var. senegal-durum wheat intercropping source. Strong isotopic evidence of below-ground N transfer occurred under high-P pot culture with root contact, averaging about 14% of wheat total N after 21 days; rhizobox conditions excluding direct root contact showed minimal evidence of transfer. The source is retained as context-indexed interplant-transfer evidence, not field-scale fertilizer replacement."
  Attribution.publicAttribution

raddadEtAl2006 : Attribution.AttributedSource
raddadEtAl2006 = Attribution.mkDOISource
  "El Amin Yousif Raddad; Olavi Luukkanen; Ahmed Ali Salih; Vesa Kaarakka; Mohamed Ahmed Elfadl"
  "Productivity and nutrient cycling in young Acacia senegal farming systems on Vertisol in the Blue Nile region, Sudan"
  "Agroforestry Systems 68:193-207"
  "2006"
  raddadEtAl2006DOI
  "https://doi.org/10.1007/s10457-006-9009-6"
  Attribution.academicArticleSource
  "Four-year Blue Nile field nutrient-budget source across Acacia senegal spacing and sorghum/sesame systems. Treatment-level N balances include both gains and losses, while below-ground biomass was not included in the reported balance. This source constrains whole-system promotion rather than proving universal positive N balance."
  Attribution.publicAttribution

deansEtAl1999 : Attribution.AttributedSource
deansEtAl1999 = Attribution.mkDOISource
  "J. D. Deans; O. Diagne; D. K. Lindley; M. Dione; J. A. Parkinson"
  "Nutrient and organic-matter accumulation in Acacia senegal fallows over 18 years"
  "Forest Ecology and Management 124(2-3):153-167"
  "1999"
  deansEtAl1999DOI
  "https://doi.org/10.1016/S0378-1127(99)00063-8"
  Attribution.academicArticleSource
  "Northern Senegal fallow chronosequence source quantifying tree/soil nutrient accumulation from ages 3-18 years. Surface-soil N increased with age/spacing, but biomass and fodder export alter site nutrient budgets; management/export therefore remains a live coordinate."
  Attribution.publicAttribution

fallEtAl2012 : Attribution.AttributedSource
fallEtAl2012 = Attribution.mkDOISource
  "Dioumacor Fall; Diegane Diouf; Alzouma Mayaki Zoubeirou; Niokhor Bakhoum; Aliou Faye; Saidou Nourou Sall"
  "Effect of distance and depth on microbial biomass and mineral nitrogen content under Acacia senegal (L.) Willd. trees"
  "Journal of Environmental Management 95 Suppl:S260-S264"
  "2012"
  fallEtAl2012DOI
  "https://doi.org/10.1016/j.jenvman.2011.03.038"
  Attribution.academicArticleSource
  "Field source sampling Acacia senegal rhizosphere soil by distance from tree stem, soil depth and dry/wet season. Mineral-N and microbial observations are retained as observer-geometry-indexed ecosystem measurements rather than a scalar BNF output."
  Attribution.publicAttribution

elTahirEtAl2009 : Attribution.AttributedSource
elTahirEtAl2009 = Attribution.mkDOISource
  "B. A. El Tahir; D. M. Ahmed; Jonas Ardo; A. M. Gaafar; A. A. Salih"
  "Changes in soil properties following conversion of Acacia senegal plantation to other land management systems in North Kordofan State, Sudan"
  "Journal of Arid Environments 73(4-5):499-505"
  "2009"
  elTahirEtAl2009DOI
  "https://doi.org/10.1016/j.jaridenv.2008.11.007"
  Attribution.academicArticleSource
  "North Kordofan land-use-transition source following conversion of a six-year Acacia senegal plantation through three cropping seasons. Aggregated mean OC/N/P concentrations and OC/N/P/K stocks declined across the reported land-management systems, so prior plantation nutrient accumulation is not identified with persistent post-conversion nutrient stock."
  Attribution.publicAttribution

basgaEtAl2018 : Attribution.AttributedSource
basgaEtAl2018 = Attribution.mkDOISource
  "Simon Djakba Basga; Oumarou Palou Madi; Jules Balna; Fanta Chimene Abib; Desire Tsozue; Aboubakar Njiemoun"
  "Sandy soil fertility restoration and crops yields after conversion of long term Acacia senegal planted fallows in North Cameroon"
  "African Journal of Agricultural Research 13(40):2154-2162"
  "2018"
  basgaEtAl2018DOI
  "https://doi.org/10.5897/AJAR2018.13283"
  Attribution.academicArticleSource
  "North Cameroon post-fallow crop-yield source. Sorghum and cowpea trials compared continuous cropping and alternative Acacia fallow conversion treatments, but every replicated treatment received a 4 g NPK 20-10-10 microdose per planting hole. Yield differences are therefore retained with mineral-fertilizer cotreatment and cannot serve as an avoided-mineral-N receipt."
  Attribution.publicAttribution

data TransferBudgetEvidenceRole : Set where
  plantFixedNContribution : TransferBudgetEvidenceRole
  interplantNitrogenTransfer : TransferBudgetEvidenceRole
  treatmentFieldNitrogenBalance : TransferBudgetEvidenceRole
  longTermSiteNutrientAccumulation : TransferBudgetEvidenceRole
  spatialSeasonalMineralNObservation : TransferBudgetEvidenceRole
  postConversionNutrientPersistence : TransferBudgetEvidenceRole
  coFertilizedCropYield : TransferBudgetEvidenceRole
  harvestExportPressure : TransferBudgetEvidenceRole

record TransferBudgetReceipt : Set where
  constructor transfer-budget-receipt
  field
    source : Attribution.AttributedSource
    sourceDOI : String
    role : TransferBudgetEvidenceRole
    temporalReading : String
    spatialReading : String
    contextReading : String
    directInterplantTransferEvidence : Bool
    wholeFieldBudgetEvidence : Bool
    fertilizerSubstitutionEvidence : Bool
open TransferBudgetReceipt public

acaciaToWheatTransferReceipt : TransferBudgetReceipt
acaciaToWheatTransferReceipt = transfer-budget-receipt
  isaacHinsingerHarmand2012
  isaacHinsingerHarmand2012DOI
  interplantNitrogenTransfer
  "21-day interspecific contact window after pre-conditioning"
  "controlled pot/rhizobox system"
  "transfer response indexed by P status and direct-root-contact regime"
  true false false

blueNileFieldBudgetReceipt : TransferBudgetReceipt
blueNileFieldBudgetReceipt = transfer-budget-receipt
  raddadEtAl2006
  raddadEtAl2006DOI
  treatmentFieldNitrogenBalance
  "four years of field cropping"
  "Blue Nile Vertisol agroforestry treatments"
  "tree spacing and associated crop remain indexed; below-ground tree biomass omitted from the reported balance"
  false true false

senegalLongTermNutrientReceipt : TransferBudgetReceipt
senegalLongTermNutrientReceipt = transfer-budget-receipt
  deansEtAl1999
  deansEtAl1999DOI
  longTermSiteNutrientAccumulation
  "3-18 year fallow chronosequence"
  "northern Senegal plantations at differing tree spacing"
  "soil/tissue nutrient accumulation and potential biomass/fodder export retained together"
  false true false

fallSpatialSeasonalMineralNReceipt : TransferBudgetReceipt
fallSpatialSeasonalMineralNReceipt = transfer-budget-receipt
  fallEtAl2012
  fallEtAl2012DOI
  spatialSeasonalMineralNObservation
  "dry-season and wet-season field sampling"
  "distance from tree stem crossed with 0-25, 25-50 and 50-75 cm soil depths"
  "soil mineral N and microbial biomass are indexed by observer geometry and season; not identified with fixation flux"
  false false false

northKordofanConversionReceipt : TransferBudgetReceipt
northKordofanConversionReceipt = transfer-budget-receipt
  elTahirEtAl2009
  elTahirEtAl2009DOI
  postConversionNutrientPersistence
  "three cropping seasons after conversion of a six-year plantation"
  "North Kordofan land-management systems with pure/intercropped crops and high/low retained-tree density"
  "previous plantation state, conversion regime, retained-tree density and subsequent cropping history remain explicit"
  false true false

cameroonCoFertilizedCropYieldReceipt : TransferBudgetReceipt
cameroonCoFertilizedCropYieldReceipt = transfer-budget-receipt
  basgaEtAl2018
  basgaEtAl2018DOI
  coFertilizedCropYield
  "two consecutive post-conversion growing seasons: sorghum then cowpea"
  "three North Cameroon sites and fallow conversion treatments"
  "all replicated crop treatments received 4 g NPK 20-10-10 per planting hole; crop yield therefore does not isolate an avoided-mineral-N counterfactual"
  false false false

------------------------------------------------------------------------
-- Canonical ladder remains authoritative.
------------------------------------------------------------------------

genericSeasonalDemandStillOpen :
  Chemistry.stageClosed Chemistry.seasonalCropNDemand ≡ false
genericSeasonalDemandStillOpen = refl

genericAvoidedMineralNStillOpen :
  Chemistry.stageClosed Chemistry.avoidedMineralN ≡ false
genericAvoidedMineralNStillOpen = refl

raddadPlantEvidenceReused : PlantN.PlantFixedNEvidence
raddadPlantEvidenceReused = PlantN.raddadProvenanceTemporalFoliarEvidence

referencePlantObserverFirewallReused :
  Measurement.rawDelta15NEqualsNdfa Measurement.canonicalMeasurementBoundary ≡ false
referencePlantObserverFirewallReused = refl

record TransferBudgetBoundary : Set where
  constructor transfer-budget-boundary
  field
    acaciaInterplantTransferEvidenceExists : Bool
    plantFixedNContributionImpliesInterplantTransfer : Bool
    transferMustRemainRootContactPAndTimeIndexed : Bool
    interplantTransferImpliesPositiveFieldNBalance : Bool
    fieldNBalanceMustRemainTreatmentAndTimeIndexed : Bool
    abovegroundBudgetEqualsWholeSystemNBalance : Bool
    soilMineralNObserverGeometryMayBeDropped : Bool
    priorNutrientAccumulationImpliesPersistentPostConversionStock : Bool
    landUseTransitionAndHistoryMustRemainIndexed : Bool
    cropYieldUnderCoAppliedMineralNClosesAvoidedMineralN : Bool
    mineralFertilizerCotreatmentMustRemainIndexed : Bool
    positiveNBalanceImpliesFertilizerSubstitution : Bool
    fertilizerSubstitutionImpliesDeploymentAuthority : Bool
    harvestAndExportMustRemainIndexed : Bool
    fieldBudgetClosesGenericSeasonalDemand : Bool
    fieldBudgetClosesGenericAvoidedMineralN : Bool
open TransferBudgetBoundary public

canonicalTransferBudgetBoundary : TransferBudgetBoundary
canonicalTransferBudgetBoundary = transfer-budget-boundary
  true false true false true false false false true false true false false true false false

acaciaTransferEvidencePaid :
  acaciaInterplantTransferEvidenceExists canonicalTransferBudgetBoundary ≡ true
acaciaTransferEvidencePaid = refl

genericSeasonalDemandNotPromoted :
  fieldBudgetClosesGenericSeasonalDemand canonicalTransferBudgetBoundary ≡ false
genericSeasonalDemandNotPromoted = refl

genericAvoidedMineralNNotPromoted :
  fieldBudgetClosesGenericAvoidedMineralN canonicalTransferBudgetBoundary ≡ false
genericAvoidedMineralNNotPromoted = refl

attributionRule : String
attributionRule =
  "Isaac, Hinsinger & Harmand 2012 (DOI 10.1016/j.scitotenv.2011.12.071; PMID 22446108) owns its controlled Acacia-to-wheat below-ground N-transfer propositions. Raddad et al. 2006 (DOI 10.1007/s10457-006-9009-6) owns its four-year Blue Nile treatment nutrient-budget propositions, including omission of below-ground biomass from the reported balance. Deans et al. 1999 (DOI 10.1016/S0378-1127(99)00063-8) owns its long-term Senegal nutrient-accumulation and harvest/export propositions. Fall et al. 2012 (DOI 10.1016/j.jenvman.2011.03.038; PMID 21514716) owns its distance/depth/season-indexed soil mineral-N and microbial observations. El Tahir et al. 2009 (DOI 10.1016/j.jaridenv.2008.11.007) owns its post-conversion North Kordofan soil nutrient-stock propositions. Basga et al. 2018 (DOI 10.5897/AJAR2018.13283) owns its North Cameroon soil-fertility and co-fertilized sorghum/cowpea yield propositions; the universal 4 g NPK 20-10-10 microdose in replicated treatments is retained as a confounding/intervention coordinate, so the crop-yield result is not an avoided-mineral-N receipt. DASHI owns the typed evidence-role chain and no-promotion boundary. None of these sources alone supplies generic seasonal crop-N-demand closure, counterfactual avoided-mineral-N quantity, universal fertilizer-substitution rule, or deployment authority."
