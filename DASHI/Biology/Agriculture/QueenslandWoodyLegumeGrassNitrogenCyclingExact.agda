module DASHI.Biology.Agriculture.QueenslandWoodyLegumeGrassNitrogenCyclingExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Biology.Agriculture.NitrogenaseChemistryCrossPollinationExact as Chemistry

------------------------------------------------------------------------
-- QUEENSLAND WOODY LEGUME <-> GRASS <-> GRAZING N CYCLING
--
-- Leucaena is used here as a Queensland woody-legume/grass comparator.
-- It is not Acacia/Senegalia same-object evidence.  The owner separates N
-- source, plant capture, grazing redistribution, soil stock and long-term
-- system state rather than calling them one generic "N benefit".
------------------------------------------------------------------------

radrizzaniEtAl2011DOI : String
radrizzaniEtAl2011DOI = "10.1071/CP10115"

conradEtAl2018DOI : String
conradEtAl2018DOI = "10.1016/j.geoderma.2017.10.029"

radrizzaniEtAl2010DOI : String
radrizzaniEtAl2010DOI = "10.1071/AN10062"

burleSheltonDalzell2003 : Attribution.AttributedSource
burleSheltonDalzell2003 = Attribution.mkNoDOISource
  "S. T. M. Burle; H. M. Shelton; S. A. Dalzell"
  "Nitrogen cycling in degraded Leucaena leucocephala-Brachiaria decumbens pastures on an acid infertile soil in south-east Queensland, Australia"
  "Tropical Grasslands 37:119-128"
  "2003"
  "https://www.tropicalgrasslands.info/public/journals/4/Historic/Tropical%20Grasslands%20Journal%20archive/PDFs/Vol_37_2003/Vol_37_02_03_pp119_128.pdf"
  Attribution.academicArticleSource
  "South-east Queensland grazing trial quantifying N pools in leucaena, signal grass, soil, cattle liveweight, faeces and urine. Nutrient imbalance constrained leucaena fixation; grazing redistributed a large fraction of consumed N through excreta. No DOI is recorded by this atlas. The source is retained as short-window N-pool/redistribution evidence, not a long-term balance or fertilizer-substitution theorem."
  Attribution.publicAttribution

radrizzaniEtAl2011 : Attribution.AttributedSource
radrizzaniEtAl2011 = Attribution.mkDOISource
  "Alejandro Radrizzani; H. Max Shelton; Scott A. Dalzell; Gunnar Kirchhof"
  "Soil organic carbon and total nitrogen under Leucaena leucocephala pastures in Queensland"
  "Crop and Pasture Science 62(4):337-345"
  "2011" radrizzaniEtAl2011DOI "https://doi.org/10.1071/CP10115"
  Attribution.academicArticleSource
  "Queensland paired-site observational study comparing long-established leucaena-grass pastures with native pasture and continuously cropped land. Surface OC/TN were higher under long-term leucaena-grass systems and varied with stand age and row position. Because suitable before/after long-term experiments were unavailable, the paired chronosequence is retained as stock-state evidence, not a longitudinal causal trajectory."
  Attribution.publicAttribution

conradEtAl2018 : Attribution.AttributedSource
conradEtAl2018 = Attribution.mkDOISource
  "Kathryn A. Conrad; Ram C. Dalal; Scott A. Dalzell; Diane E. Allen; Ryosuke Fujinuma; Neal W. Menzies"
  "Soil nitrogen status and turnover in subtropical leucaena-grass pastures as quantified by delta-15N natural abundance"
  "Geoderma 313:126-134"
  "2018" conradEtAl2018DOI "https://doi.org/10.1016/j.geoderma.2017.10.029"
  Attribution.academicArticleSource
  "Southern-Queensland leucaena-grass chronosequence and paired grass-site study sampled to 1 m. Natural-abundance isotope analysis estimated a large atmospheric contribution to leucaena N and the study observed age/depth/row-position differences in soil N stocks and turnover. The isotope estimate, soil stock and companion-grass N state remain separate empirical objects."
  Attribution.publicAttribution

radrizzaniEtAl2010 : Attribution.AttributedSource
radrizzaniEtAl2010 = Attribution.mkDOISource
  "Alejandro Radrizzani; H. Max Shelton; Scott A. Dalzell"
  "Response of Leucaena leucocephala pastures to phosphorus and sulfur application in Queensland"
  "Animal Production Science 50(10):961-975"
  "2010" radrizzaniEtAl2010DOI "https://doi.org/10.1071/AN10062"
  Attribution.academicArticleSource
  "Multi-site south-east/central Queensland fertiliser experiments showing that P/S deficiencies can directly restrict leucaena growth and suppress symbiotic N2 fixation; companion-grass competition for water/nutrients also changes response. Retained as an enablement/context receipt rather than a context-free woody-legume N-input law."
  Attribution.publicAttribution

data WoodyGrassEvidenceRole : Set where
  shortWindowGrazingNitrogenPool : WoodyGrassEvidenceRole
  longTermSoilCarbonNitrogenStock : WoodyGrassEvidenceRole
  isotopeNitrogenSourceTurnover : WoodyGrassEvidenceRole
  nutrientEnablementConstraint : WoodyGrassEvidenceRole

record WoodyGrassReceipt : Set where
  constructor woody-grass-receipt
  field
    source : Attribution.AttributedSource
    role : WoodyGrassEvidenceRole
    temporalReading : String
    spatialReading : String
    nitrogenReading : String
    consumerReading : String
    boundedReading : String
open WoodyGrassReceipt public

grazingCycleReceipt : WoodyGrassReceipt
grazingCycleReceipt = woody-grass-receipt
  burleSheltonDalzell2003 shortWindowGrazingNitrogenPool
  "short grazing trial embedded in a degraded established pasture"
  "south-east Queensland acid infertile soil; leucaena + signal grass + livestock"
  "plant/soil/animal/faecal/urinary N pools and estimated leucaena fixation"
  "system redistribution under grazing"
  "consumed N is not equivalent to animal export; excreta recycling, nutrient deficiency and soil state remain explicit"

longTermStockReceipt : WoodyGrassReceipt
longTermStockReceipt = woody-grass-receipt
  radrizzaniEtAl2011 longTermSoilCarbonNitrogenStock
  "paired systems including long-established leucaena-grass stands"
  "Queensland sites; row and inter-row stock geometry"
  "surface-soil total N and organic C accumulation"
  "long-term soil-stock state"
  "paired observational age contrast is not longitudinal before/after causality and total N stock does not identify transfer pathway"

isotopeTurnoverReceipt : WoodyGrassReceipt
isotopeTurnoverReceipt = woody-grass-receipt
  conradEtAl2018 isotopeNitrogenSourceTurnover
  "0-40 year chronosequence"
  "paired leucaena-row/grass positions sampled through the soil profile"
  "natural-abundance isotope source estimate plus soil N stocks/turnover"
  "N-source attribution and soil turnover"
  "atmospheric contribution estimate is not direct bacterial flux; soil-stock enrichment is not measured legume-to-grass transfer"

nutrientEnablementReceipt : WoodyGrassReceipt
nutrientEnablementReceipt = woody-grass-receipt
  radrizzaniEtAl2010 nutrientEnablementConstraint
  "multi-site fertiliser trials"
  "south-east and central Queensland leucaena-grass pastures"
  "P/S fertility state, leucaena response and symbiotic-fixation constraint"
  "environmental enablement of woody-legume service"
  "P/S state, soil history, acidity and companion-grass water/nutrient competition remain indexed"

------------------------------------------------------------------------
-- Generic BNF ladder remains untouched.
------------------------------------------------------------------------

genericFixedNFluxStillOpen : Chemistry.stageClosed Chemistry.bacterialFixedNFlux ≡ false
genericFixedNFluxStillOpen = refl

genericAvoidedMineralNStillOpen : Chemistry.stageClosed Chemistry.avoidedMineralN ≡ false
genericAvoidedMineralNStillOpen = refl

record WoodyLegumeGrassBoundary : Set where
  constructor woody-legume-grass-boundary
  field
    woodyLegumeFixedNImpliesCompanionGrassCapture : Bool
    soilTotalNitrogenIdentifiesLegumeToGrassTransfer : Bool
    grazingExcretaRedistributionMayBeDropped : Bool
    consumedPastureNitrogenEqualsAnimalProductExport : Bool
    pairedChronosequenceCreatesLongitudinalCausalTrajectory : Bool
    isotopeAtmosphericContributionEqualsDirectBacterialFlux : Bool
    phosphorusSulfurLimitationMayBeDroppedFromFixation : Bool
    companionGrassCompetitionMayBeDropped : Bool
    soilStockIncreaseImpliesAvoidedFertilizer : Bool
    queenslandLeucaenaCreatesAcaciaSameObjectEvidence : Bool
    queenslandLeucaenaEvidenceClosesAcaciaAvoidedMineralN : Bool
    woodyLegumeGrassEvidenceCreatesDeploymentAuthority : Bool
open WoodyLegumeGrassBoundary public

canonicalWoodyLegumeGrassBoundary : WoodyLegumeGrassBoundary
canonicalWoodyLegumeGrassBoundary = woody-legume-grass-boundary
  false false false false false false false false false false false false

attributionRule : String
attributionRule =
  "Burle, Shelton & Dalzell 2003 (Tropical Grasslands 37:119-128; no DOI recorded by this atlas) owns its south-east Queensland plant/soil/cattle/excreta N-pool propositions. Radrizzani et al. 2011 (DOI 10.1071/CP10115) owns its paired Queensland leucaena-grass/native-pasture/cropped-land soil OC/TN observations. Conrad et al. 2018 (DOI 10.1016/j.geoderma.2017.10.029) owns its delta-15N source attribution and age/depth/row-position soil-N turnover observations. Radrizzani, Shelton & Dalzell 2010 (DOI 10.1071/AN10062) owns its Queensland P/S-fertilisation, growth/fixation and companion-grass competition observations. DASHI owns only the typed N-source/redistribution/stock separation and no-promotion boundary. Leucaena evidence is not Acacia/Senegalia same-object evidence and does not close the canonical BNF or avoided-mineral-N stages."
