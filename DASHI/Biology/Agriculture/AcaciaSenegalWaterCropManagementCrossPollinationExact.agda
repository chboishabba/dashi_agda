module DASHI.Biology.Agriculture.AcaciaSenegalWaterCropManagementCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Biology.Agriculture.BNFQualifiedInterventionModelExact as BNF
import DASHI.Biology.Agriculture.AcaciaSenegalPlantNitrogenAssimilationEvidenceExact as PlantN
import DASHI.Environment.AcaciaSenegalDrylandWaterCarbonExact as Dryland

------------------------------------------------------------------------
-- ACACIA WATER <-> CROP MANAGEMENT CROSS-SITE COLLISION
------------------------------------------------------------------------

raddadLuukkanen2007DOI : String
raddadLuukkanen2007DOI = "10.1016/j.agwat.2006.06.001"

gaafarEtAl2006DOI : String
gaafarEtAl2006DOI = "10.1007/s10457-005-2918-y"

raddadLuukkanenWUE2006DOI : String
raddadLuukkanenWUE2006DOI = "10.1016/j.foreco.2006.01.036"

raddadLuukkanen2007 : Attribution.AttributedSource
raddadLuukkanen2007 = Attribution.mkDOISource
  "El Amin Yousif Raddad; Olavi Luukkanen"
  "The influence of different Acacia senegal agroforestry systems on soil water and crop yields in clay soils of the Blue Nile region, Sudan"
  "Agricultural Water Management 87(1):61-72"
  "2007"
  raddadLuukkanen2007DOI
  "https://doi.org/10.1016/j.agwat.2006.06.001"
  Attribution.academicArticleSource
  "Blue Nile clay-soil source comparing Acacia senegal spacing and pure/intercropped sorghum or sesame. Soil water was observed at multiple depths and crop stages. In the reported four-year-old systems there was little water competition and no significant sorghum yield difference between intercropped and pure cultivation; the authors explicitly caution that resource capture can change as the system matures."
  Attribution.publicAttribution

gaafarEtAl2006 : Attribution.AttributedSource
gaafarEtAl2006 = Attribution.mkDOISource
  "Abdalla Mohamed Gaafar; A. A. Salih; Olavi Luukkanen; Mohamed Ahmed El Fadl; Vesa Kaarakka"
  "Improving the traditional Acacia senegal-crop system in Sudan: the effect of tree density on water use, gum production and crop yields"
  "Agroforestry Systems 66(1):1-11"
  "2006"
  gaafarEtAl2006DOI
  "https://doi.org/10.1007/s10457-005-2918-y"
  Attribution.academicArticleSource
  "North Kordofan sandy-soil source varying Acacia senegal tree density with sorghum and karkadeh, and measuring physiological interactions, yield and soil-water depletion. The reported system showed tree-crop competition for soil water; this is retained as a contrasting site/soil-context proposition rather than a universal species effect."
  Attribution.publicAttribution

raddadLuukkanenWUE2006 : Attribution.AttributedSource
raddadLuukkanenWUE2006 = Attribution.mkDOISource
  "El Amin Yousif Raddad; Olavi Luukkanen"
  "Adaptive genetic variation in water-use efficiency and gum yield in Acacia senegal provenances grown on clay soil in the Blue Nile region, Sudan"
  "Forest Ecology and Management 226(1-3):219-229"
  "2006"
  raddadLuukkanenWUE2006DOI
  "https://doi.org/10.1016/j.foreco.2006.01.036"
  Attribution.academicArticleSource
  "Blue Nile common-site source comparing eight Acacia senegal provenances for growth, carbon-isotope water-use-efficiency proxy and gum production. Provenance groups differed in delta-13C and productivity traits. This source is not joined numerically to the separate Raddad et al. 2005 Ndfa paper merely because the papers use eight provenance labels and a Blue Nile clay-site setting."
  Attribution.publicAttribution

data WaterCropEvidenceRole : Set where
  claySoilWaterCropResponse : WaterCropEvidenceRole
  sandySoilWaterCropResponse : WaterCropEvidenceRole
  provenanceWaterUseGumResponse : WaterCropEvidenceRole
  cropYieldResponse : WaterCropEvidenceRole
  managementDensityResponse : WaterCropEvidenceRole

record WaterCropContextReceipt : Set where
  constructor water-crop-context-receipt
  field
    source : Attribution.AttributedSource
    sourceDOI : String
    soilContext : String
    treeAgeContext : String
    densityAndManagement : String
    cropContext : String
    waterObservation : String
    boundedOutcome : String
open WaterCropContextReceipt public

blueNileClayReceipt : WaterCropContextReceipt
blueNileClayReceipt = water-crop-context-receipt
  raddadLuukkanen2007
  raddadLuukkanen2007DOI
  "Blue Nile clay soil"
  "approximately four-year-old agroforestry systems"
  "5 x 5 m or 10 x 10 m spacing; trees alone or intercropped"
  "sorghum and sesame"
  "neutron-probe soil water at 0-25, 25-50 and 50-75 cm and early/mid/late crop stages"
  "little water competition in the reported early-stage system; no significant sorghum yield difference between intercropped and pure cultivation"

northKordofanSandReceipt : WaterCropContextReceipt
northKordofanSandReceipt = water-crop-context-receipt
  gaafarEtAl2006
  gaafarEtAl2006DOI
  "North Kordofan sandy soil"
  "traditional/improved Acacia senegal crop-system context"
  "266 or 433 trees per hectare"
  "early-maturing sorghum and karkadeh"
  "soil-water depletion and physiological interactions"
  "tree-crop competition for soil water in the reported sandy-soil system"

blueNileProvenanceWUEReceipt : WaterCropContextReceipt
blueNileProvenanceWUEReceipt = water-crop-context-receipt
  raddadLuukkanenWUE2006
  raddadLuukkanenWUE2006DOI
  "Blue Nile clay common garden with provenances originating from contrasting sand/clay environments"
  "multi-year tree growth / gum-production observation"
  "eight provenance identities; provenance-of-origin environment retained"
  "tree growth and gum production rather than an associated cereal crop"
  "leaf and branch-wood delta-13C as a water-use-efficiency/adaptation proxy plus soil-water observations"
  "provenance groups differ in water-use proxy, growth and gum traits; no Ndfa correlation is manufactured by joining to a separate provenance paper"

------------------------------------------------------------------------
-- Reuse existing plant-N and hydrology/ecological consumer surfaces.
------------------------------------------------------------------------

drylandWaterCarbonBoundaryReused : Dryland.AcaciaLESWeld
drylandWaterCarbonBoundaryReused = Dryland.canonicalAcaciaLESWeld

raddadNdfaEvidenceReused : PlantN.PlantFixedNEvidence
raddadNdfaEvidenceReused = PlantN.raddadProvenanceTemporalFoliarEvidence

ecologicalConsumerRequiresHydrology :
  BNF.requiredFor BNF.predictEcologicalResponse BNF.hydrologyAdequacy ≡ true
ecologicalConsumerRequiresHydrology = refl

record WaterCropBoundary : Set where
  constructor water-crop-boundary
  field
    crossSiteContrastRetained : Bool
    speciesAndDensityDetermineWaterCompetition : Bool
    soilHydraulicContextMustRemainIndexed : Bool
    treeAgeMustRemainIndexed : Bool
    cropAndManagementMustRemainIndexed : Bool
    earlyStageNoYieldPenaltyImpliesMatureSystemNoYieldPenalty : Bool
    cropYieldAloneIdentifiesWaterCompetitionMechanism : Bool
    sharedProvenanceLabelsCreateNdfaWUEGumCorrelation : Bool
    crossPaperSameEmpiricalObjectMayBeAssumed : Bool
    provenanceOriginEnvironmentMustRemainIndexed : Bool
    sourceContrastCreatesSameEmpiricalObject : Bool
    waterCropEvidenceCreatesDeploymentAuthority : Bool
open WaterCropBoundary public

canonicalWaterCropBoundary : WaterCropBoundary
canonicalWaterCropBoundary = water-crop-boundary
  true false true true true false false false false true false false

attributionRule : String
attributionRule =
  "Raddad & Luukkanen 2007 (DOI 10.1016/j.agwat.2006.06.001) owns its Blue Nile clay-soil water/crop propositions, including the bounded early-stage little-competition result and explicit maturity caution. Gaafar et al. 2006 (DOI 10.1007/s10457-005-2918-y) owns its North Kordofan sandy-soil tree-density/water/crop propositions. Raddad & Luukkanen 2006 (DOI 10.1016/j.foreco.2006.01.036) owns its eight-provenance delta-13C/water-use/growth/gum propositions. Raddad et al. 2005 (DOI 10.1007/s11104-005-2152-4), imported via the plant-N owner, separately owns its provenance-indexed Ndfa propositions. DASHI owns the cross-site/context and cross-paper attribution firewalls. Shared provenance labels do not create a cross-paper Ndfa-WUE-gum correlation or same empirical object without an explicit join receipt."
