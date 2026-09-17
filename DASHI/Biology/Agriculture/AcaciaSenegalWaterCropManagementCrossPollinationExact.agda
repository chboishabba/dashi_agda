module DASHI.Biology.Agriculture.AcaciaSenegalWaterCropManagementCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Biology.Agriculture.BNFQualifiedInterventionModelExact as BNF
import DASHI.Environment.AcaciaSenegalDrylandWaterCarbonExact as Dryland

------------------------------------------------------------------------
-- ACACIA WATER <-> CROP MANAGEMENT CROSS-SITE COLLISION
--
-- Same species and related management coordinates do not determine one
-- universal water-competition/crop-yield response across contrasting soils.
------------------------------------------------------------------------

raddadLuukkanen2007DOI : String
raddadLuukkanen2007DOI = "10.1016/j.agwat.2006.06.001"

gaafarEtAl2006DOI : String
gaafarEtAl2006DOI = "10.1007/s10457-005-2918-y"

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

data WaterCropEvidenceRole : Set where
  claySoilWaterCropResponse : WaterCropEvidenceRole
  sandySoilWaterCropResponse : WaterCropEvidenceRole
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

------------------------------------------------------------------------
-- Reuse the existing hydrology/ecological consumer surfaces.
------------------------------------------------------------------------

drylandWaterCarbonBoundaryReused : Dryland.AcaciaLESWeld
drylandWaterCarbonBoundaryReused = Dryland.canonicalAcaciaLESWeld

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
    sourceContrastCreatesSameEmpiricalObject : Bool
    waterCropEvidenceCreatesDeploymentAuthority : Bool
open WaterCropBoundary public

canonicalWaterCropBoundary : WaterCropBoundary
canonicalWaterCropBoundary = water-crop-boundary
  true false true true true false false false false

attributionRule : String
attributionRule =
  "Raddad & Luukkanen 2007 (DOI 10.1016/j.agwat.2006.06.001) owns its Blue Nile clay-soil water/crop propositions, including the bounded early-stage little-competition result and explicit maturity caution. Gaafar et al. 2006 (DOI 10.1007/s10457-005-2918-y) owns its North Kordofan sandy-soil tree-density/water/crop propositions. DASHI owns the cross-site context separation and no-promotion boundary. Contrasting sources do not become one empirical object, and neither supplies universal water-competition, yield, or deployment authority."
