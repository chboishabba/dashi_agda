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
-- Queensland Leucaena evidence is the local system surface. Catchpoole &
-- Blair 1990 Parts II-III remain external mechanism/method donors. Vallis
-- 1983 is a Queensland field residue-transfer receipt. None of these routes
-- are silently identified with contemporaneous living-root transfer.
------------------------------------------------------------------------

radrizzaniEtAl2011DOI : String
radrizzaniEtAl2011DOI = "10.1071/CP10115"

conradEtAl2018DOI : String
conradEtAl2018DOI = "10.1016/j.geoderma.2017.10.029"

radrizzaniEtAl2010DOI : String
radrizzaniEtAl2010DOI = "10.1071/AN10062"

catchpooleBlair1990TransferDOI : String
catchpooleBlair1990TransferDOI = "10.1071/AR9900531"

catchpooleBlair1990ResidueDOI : String
catchpooleBlair1990ResidueDOI = "10.1071/AR9900539"

vallis1983DOI : String
vallis1983DOI = "10.1071/AR9830367"

sierraNygren2006DOI : String
sierraNygren2006DOI = "10.1016/j.soilbio.2005.12.012"

burleSheltonDalzell2003 : Attribution.AttributedSource
burleSheltonDalzell2003 = Attribution.mkNoDOISource
  "S. T. M. Burle; H. M. Shelton; S. A. Dalzell"
  "Nitrogen cycling in degraded Leucaena leucocephala-Brachiaria decumbens pastures on an acid infertile soil in south-east Queensland, Australia"
  "Tropical Grasslands 37:119-128"
  "2003"
  "https://www.tropicalgrasslands.info/public/journals/4/Historic/Tropical%20Grasslands%20Journal%20archive/PDFs/Vol_37_2003/Vol_37_02_03_pp119_128.pdf"
  Attribution.academicArticleSource
  "South-east Queensland grazing trial quantifying N pools in leucaena, signal grass, soil, cattle liveweight, faeces and urine. Nutrient imbalance constrained leucaena fixation; grazing redistributed a large fraction of consumed N through excreta. No DOI is recorded by this atlas. Short-window N-pool/redistribution evidence only."
  Attribution.publicAttribution

radrizzaniEtAl2011 : Attribution.AttributedSource
radrizzaniEtAl2011 = Attribution.mkDOISource
  "Alejandro Radrizzani; H. Max Shelton; Scott A. Dalzell; Gunnar Kirchhof"
  "Soil organic carbon and total nitrogen under Leucaena leucocephala pastures in Queensland"
  "Crop and Pasture Science 62(4):337-345"
  "2011" radrizzaniEtAl2011DOI "https://doi.org/10.1071/CP10115"
  Attribution.academicArticleSource
  "Queensland paired-site observational comparison of long-established leucaena-grass pasture, native pasture and continuously cropped land. Surface OC/TN varied with stand age and row position. The paired chronosequence is stock-state evidence rather than longitudinal before/after causality."
  Attribution.publicAttribution

conradEtAl2018 : Attribution.AttributedSource
conradEtAl2018 = Attribution.mkDOISource
  "Kathryn A. Conrad; Ram C. Dalal; Scott A. Dalzell; Diane E. Allen; Ryosuke Fujinuma; Neal W. Menzies"
  "Soil nitrogen status and turnover in subtropical leucaena-grass pastures as quantified by delta-15N natural abundance"
  "Geoderma 313:126-134"
  "2018" conradEtAl2018DOI "https://doi.org/10.1016/j.geoderma.2017.10.029"
  Attribution.academicArticleSource
  "Southern-Queensland leucaena-grass chronosequence and paired grass-site study to 1 m. Natural-abundance isotope analysis estimated atmospheric contribution to leucaena N and observed age/depth/row-position soil-N differences. Source attribution, soil stock and companion-grass state remain separate."
  Attribution.publicAttribution

radrizzaniEtAl2010 : Attribution.AttributedSource
radrizzaniEtAl2010 = Attribution.mkDOISource
  "Alejandro Radrizzani; H. Max Shelton; Scott A. Dalzell"
  "Response of Leucaena leucocephala pastures to phosphorus and sulfur application in Queensland"
  "Animal Production Science 50(10):961-975"
  "2010" radrizzaniEtAl2010DOI "https://doi.org/10.1071/AN10062"
  Attribution.academicArticleSource
  "Multi-site Queensland fertiliser experiments showing P/S deficiencies can restrict leucaena growth and suppress symbiotic N2 fixation, while companion-grass competition for water/nutrients changes response. Environmental-enablement receipt, not a context-free woody-legume N-input law."
  Attribution.publicAttribution

catchpooleBlair1990Transfer : Attribution.AttributedSource
catchpooleBlair1990Transfer = Attribution.mkDOISource
  "D. W. Catchpoole; Graeme J. Blair"
  "Forage tree legumes. II. Investigation of nitrogen transfer to an associated grass using a split-root technique"
  "Australian Journal of Agricultural Research 41(3):531-537"
  "1990" catchpooleBlair1990TransferDOI "https://doi.org/10.1071/AR9900531"
  Attribution.academicArticleSource
  "Controlled split-root 15N transfer experiment following a South-Sulawesi field experiment in the same publication series. The earlier field system found no significant tree-legume-to-Panicum N transfer, while the controlled split-root system detected a small labelled transfer over weeks. Retained as an experimental-scale donor: detectable controlled transfer is not identified with field transfer and is not Queensland same-object evidence."
  Attribution.publicAttribution

catchpooleBlair1990Residue : Attribution.AttributedSource
catchpooleBlair1990Residue = Attribution.mkDOISource
  "D. W. Catchpoole; Graeme J. Blair"
  "Forage tree legumes. III. Release of nitrogen from leaf, faeces and urine derived from Leucaena and Gliricidia leaf"
  "Australian Journal of Agricultural Research 41(3):539-547"
  "1990" catchpooleBlair1990ResidueDOI "https://doi.org/10.1071/AR9900539"
  Attribution.academicArticleSource
  "Controlled 15N-labelled residue experiment comparing tree-legume leaf, faeces and urine, placement/incorporation and subsequent Panicum capture/mineral soil N over ten weeks. Recovery differed strongly by residue form and placement. Retained as a route/placement donor rather than field grazing or Queensland same-object evidence."
  Attribution.publicAttribution

vallis1983 : Attribution.AttributedSource
vallis1983 = Attribution.mkDOISource
  "I. Vallis"
  "Uptake by grass and transfer to soil of nitrogen from 15N-labelled legume materials applied to a Rhodes grass pasture"
  "Australian Journal of Agricultural Research 34(4):367-376"
  "1983" vallis1983DOI "https://doi.org/10.1071/AR9830367"
  Attribution.academicArticleSource
  "South-eastern Queensland field tracer study applying 15N-labelled Siratro and Greenleaf desmodium residues to a Rhodes-grass pasture and following labelled N in grass/soil over one to three years. It is a field residue-transfer receipt, not evidence for contemporaneous living-root or direct below-ground legume-to-grass transfer."
  Attribution.publicAttribution


sierraNygren2006 : Attribution.AttributedSource
sierraNygren2006 = Attribution.mkDOISource
  "Jorge Sierra; Pekka Nygren"
  "Transfer of N fixed by a legume tree to the associated grass in a tropical silvopastoral system"
  "Soil Biology and Biochemistry 38(7):1893-1903"
  "2006" sierraNygren2006DOI "https://doi.org/10.1016/j.soilbio.2005.12.012"
  Attribution.academicArticleSource
  "Guadeloupe field silvopastoral experiment using 15N natural abundance with Gliricidia sepium and Dichanthium aristatum. Above-ground litter/excreta recycling was excluded from the system, atmospheric-origin N in grass was associated with tree fine-root density, and reference-plant selection required explicit treatment because roots invaded neighbouring grass plots and soil isotope baselines differed. Retained as an external field route-discrimination and experimental-design donor, not Queensland or Acacia/Senegalia same-object evidence."
  Attribution.publicAttribution

data WoodyGrassEvidenceRole : Set where
  shortWindowGrazingNitrogenPool : WoodyGrassEvidenceRole
  longTermSoilCarbonNitrogenStock : WoodyGrassEvidenceRole
  isotopeNitrogenSourceTurnover : WoodyGrassEvidenceRole
  nutrientEnablementConstraint : WoodyGrassEvidenceRole
  controlledLegumeToGrassTransfer : WoodyGrassEvidenceRole
  residueExcretaNitrogenRelease : WoodyGrassEvidenceRole
  fieldResidueNitrogenTransfer : WoodyGrassEvidenceRole
  fieldBelowGroundTransferDesign : WoodyGrassEvidenceRole

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
  "short grazing trial in an established degraded pasture"
  "south-east Queensland leucaena + signal grass + livestock"
  "plant/soil/animal/faecal/urinary N pools and estimated leucaena fixation"
  "system redistribution under grazing"
  "consumed N is not animal export; excreta recycling, nutrient deficiency and soil state remain explicit"

longTermStockReceipt : WoodyGrassReceipt
longTermStockReceipt = woody-grass-receipt
  radrizzaniEtAl2011 longTermSoilCarbonNitrogenStock
  "long-established paired pasture/cropping systems"
  "Queensland sites; row/inter-row stock geometry"
  "surface-soil total N and organic C"
  "long-term soil-stock state"
  "paired age contrast is not longitudinal causality and stock does not identify transfer pathway"

isotopeTurnoverReceipt : WoodyGrassReceipt
isotopeTurnoverReceipt = woody-grass-receipt
  conradEtAl2018 isotopeNitrogenSourceTurnover
  "0-40 year chronosequence"
  "paired leucaena-row/grass positions through soil profile"
  "natural-abundance source estimate plus soil-N stocks/turnover"
  "N-source attribution and soil turnover"
  "atmospheric contribution estimate is not direct bacterial flux or measured grass-transfer flux"

nutrientEnablementReceipt : WoodyGrassReceipt
nutrientEnablementReceipt = woody-grass-receipt
  radrizzaniEtAl2010 nutrientEnablementConstraint
  "multi-site fertiliser trials"
  "south-east and central Queensland leucaena-grass pastures"
  "P/S state, leucaena response and fixation constraint"
  "environmental enablement"
  "soil history, acidity and grass water/nutrient competition remain indexed"

controlledTransferReceipt : WoodyGrassReceipt
controlledTransferReceipt = woody-grass-receipt
  catchpooleBlair1990Transfer controlledLegumeToGrassTransfer
  "6-12 week controlled split-root tracer observation"
  "controlled tree/grass root system; field predecessor in South Sulawesi remains a different object"
  "labelled N movement from tree-legume source to grass"
  "direct-transfer detectability"
  "controlled transfer does not imply detectable field transfer and does not create Queensland evidence"

routePlacementReceipt : WoodyGrassReceipt
routePlacementReceipt = woody-grass-receipt
  catchpooleBlair1990Residue residueExcretaNitrogenRelease
  "ten-week controlled residue/mineralisation assay"
  "labelled leaf/faeces/urine; surface versus incorporated placement; Panicum receiver"
  "source-resolved N release, soil mineral N and grass capture"
  "transport-route/placement sensitivity"
  "leaf, faeces and urine are distinct transport states; placement and volatilisation context cannot be erased"

fieldResidueTransferReceipt : WoodyGrassReceipt
fieldResidueTransferReceipt = woody-grass-receipt
  vallis1983 fieldResidueNitrogenTransfer
  "one-to-three-year field tracer follow-up"
  "south-eastern Queensland Rhodes-grass pasture receiving surface-applied labelled legume residues"
  "15N-labelled residue disappearance plus recovery in companion grass and soil"
  "field residue-mediated companion-grass capture"
  "residue-mediated transfer is a decomposer/mineralisation route and is not contemporaneous living-legume or direct below-ground transfer"


fieldBelowGroundTransferDesignReceipt : WoodyGrassReceipt
fieldBelowGroundTransferDesignReceipt = woody-grass-receipt
  sierraNygren2006 fieldBelowGroundTransferDesign
  "field observation with below-ground-only N recycling plus supporting reference-plant assay"
  "Guadeloupe Gliricidia-Dichanthium silvopastoral plots; external to Australia"
  "15N natural-abundance atmospheric-origin signal in grass evaluated against tree-root density and soil isotope baselines"
  "route-discriminating experimental design"
  "suggests direct below-ground transfer in its source system while retaining reference-plant, root-invasion and isotope-baseline problems; does not create Queensland or Acacia/Senegalia same-object evidence"

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
    controlledTransferImpliesFieldTransfer : Bool
    leafFaecesUrineTransportRouteMayBeDropped : Bool
    residuePlacementMayBeDroppedFromNitrogenCapture : Bool
    fieldResidueTransferImpliesLivingLegumeTransfer : Bool
    externalTransferDonorCreatesQueenslandSameObjectReceipt : Bool
    externalFieldBelowGroundTransferCreatesQueenslandSameObjectReceipt : Bool
    belowGroundTransferReferencePlantProblemMayBeDropped : Bool
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
canonicalWoodyLegumeGrassBoundary = record
  { woodyLegumeFixedNImpliesCompanionGrassCapture = false
  ; soilTotalNitrogenIdentifiesLegumeToGrassTransfer = false
  ; grazingExcretaRedistributionMayBeDropped = false
  ; consumedPastureNitrogenEqualsAnimalProductExport = false
  ; controlledTransferImpliesFieldTransfer = false
  ; leafFaecesUrineTransportRouteMayBeDropped = false
  ; residuePlacementMayBeDroppedFromNitrogenCapture = false
  ; fieldResidueTransferImpliesLivingLegumeTransfer = false
  ; externalTransferDonorCreatesQueenslandSameObjectReceipt = false
  ; externalFieldBelowGroundTransferCreatesQueenslandSameObjectReceipt = false
  ; belowGroundTransferReferencePlantProblemMayBeDropped = false
  ; pairedChronosequenceCreatesLongitudinalCausalTrajectory = false
  ; isotopeAtmosphericContributionEqualsDirectBacterialFlux = false
  ; phosphorusSulfurLimitationMayBeDroppedFromFixation = false
  ; companionGrassCompetitionMayBeDropped = false
  ; soilStockIncreaseImpliesAvoidedFertilizer = false
  ; queenslandLeucaenaCreatesAcaciaSameObjectEvidence = false
  ; queenslandLeucaenaEvidenceClosesAcaciaAvoidedMineralN = false
  ; woodyLegumeGrassEvidenceCreatesDeploymentAuthority = false
  }

attributionRule : String
attributionRule =
  "Burle, Shelton & Dalzell 2003 (Tropical Grasslands 37:119-128; no DOI recorded by this atlas) owns its south-east Queensland plant/soil/cattle/excreta N-pool observations. Radrizzani et al. 2011 (DOI 10.1071/CP10115) owns its paired Queensland soil OC/TN observations. Conrad et al. 2018 (DOI 10.1016/j.geoderma.2017.10.029) owns its delta-15N source attribution and soil-N turnover observations. Radrizzani, Shelton & Dalzell 2010 (DOI 10.1071/AN10062) owns its Queensland P/S/fixation and grass-competition observations. Catchpoole & Blair 1990-II (DOI 10.1071/AR9900531) owns its controlled split-root labelled-transfer propositions and the reported contrast with the earlier South-Sulawesi field series. Catchpoole & Blair 1990-III (DOI 10.1071/AR9900539) owns its labelled leaf/faeces/urine release and placement propositions. Vallis 1983 (DOI 10.1071/AR9830367) owns its south-eastern Queensland 15N-labelled legume-residue-to-Rhodes-grass/soil field observations. Sierra & Nygren 2006 (DOI 10.1016/j.soilbio.2005.12.012) owns its Guadeloupe below-ground-only silvopastoral 15N transfer design, root-density association and reference-plant limitations. DASHI owns only the typed source/route/redistribution/stock separation and no-promotion boundary. Residue-mediated field capture is not living-root transfer; the external field below-ground donor remains method/route evidence rather than Queensland same-object transfer, and its reference-plant/isotope-baseline constraints remain explicit; and Leucaena evidence does not create Acacia/Senegalia same-object evidence or close canonical BNF/avoided-mineral-N stages."
