module DASHI.Biology.Agriculture.AustralianWattleSoilBiotaRehabilitationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attribution

bell2003DOI : String
bell2003DOI = "10.1071/SB02004"

moreiraGrez2019DOI : String
moreiraGrez2019DOI = "10.3389/fmicb.2019.01617"

kneller2018DOI : String
kneller2018DOI = "10.1016/j.scitotenv.2017.11.219"

kneller2018PMID : String
kneller2018PMID = "29197793"

bellEtAl2003 : Attribution.AttributedSource
bellEtAl2003 = Attribution.mkDOISource
  "J. Bell; Simone Wells; David A. Jasper; Lynette K. Abbott"
  "Field inoculation with arbuscular mycorrhizal fungi in rehabilitation of mine sites with native vegetation, including Acacia spp."
  "Australian Systematic Botany 16(1):131-138"
  "2003" bell2003DOI "https://doi.org/10.1071/SB02004"
  Attribution.academicArticleSource
  "Western Australian mine-rehabilitation field source. Added AM inoculum could remain infective while native-plant colonisation stayed limited; indigenous propagules, season, temperature, moisture and plant age remained relevant. No generic growth benefit is inferred from inoculum viability."
  Attribution.publicAttribution

moreiraGrezEtAl2019 : Attribution.AttributedSource
moreiraGrezEtAl2019 = Attribution.mkDOISource
  "Benjamin Moreira-Grez; et al."
  "Reconditioning Degraded Mine Site Soils With Exogenous Soil Microbes: Plant Fitness and Soil Microbiome Outcomes"
  "Frontiers in Microbiology 10:1617"
  "2019" moreiraGrez2019DOI "https://doi.org/10.3389/fmicb.2019.01617"
  Attribution.academicArticleSource
  "Pilbara Acacia ancistrocarpa mine-soil experiment with an agriculture-derived soil microbial inoculum. Exogenous consortium persistence was limited and plant-fitness responses were variable/negative; ecological matching between inoculum, host and edaphic setting remains explicit."
  Attribution.publicAttribution

knellerEtAl2018 : Attribution.AttributedSource
knellerEtAl2018 = Attribution.mkDOISource
  "Tayla Kneller; Richard J. Harris; Amber Bateman; Miriam Munoz-Rojas"
  "Native-plant amendments and topsoil addition enhance soil function in post-mining arid grasslands"
  "Science of the Total Environment 621:744-752"
  "2018" kneller2018DOI "https://pubmed.ncbi.nlm.nih.gov/29197793/"
  Attribution.academicArticleSource
  "Pilbara reconstructed-soil experiment including Triodia wiseana and mixtures with Acacia ancistrocarpa. Native amendment increased soil C/N and microbial activity but did not translate to improved emergence/survival; topsoil retained distinct establishment value."
  Attribution.publicAttribution

record WattleSoilBiotaBoundary : Set where
  constructor wattle-soil-biota-boundary
  field
    inoculumViabilityImpliesFieldColonisation : Bool
    introducedInoculumEqualsIndigenousPropagulePool : Bool
    fieldColonisationImpliesPlantGrowthBenefit : Bool
    agriculturalMicrobialInoculumImpliesNativeSystemFitness : Bool
    soilFunctionImprovementImpliesNativeRecruitment : Bool
    microbialActivityImpliesPlantSurvival : Bool
    topsoilRoleMayBeDropped : Bool
    hostSeasonTemperatureMoistureContextMustRemainIndexed : Bool
    soilBiotaResultCreatesDeploymentAuthority : Bool
open WattleSoilBiotaBoundary public

canonicalWattleSoilBiotaBoundary : WattleSoilBiotaBoundary
canonicalWattleSoilBiotaBoundary = wattle-soil-biota-boundary
  false false false false false false false true false

attributionRule : String
attributionRule =
  "Bell et al. 2003 owns its WA AM-inoculation rehabilitation observations; Moreira-Grez et al. 2019 owns its agriculture-derived SMI/Acacia ancistrocarpa mine-soil observations; Kneller et al. 2018 (DOI 10.1016/j.scitotenv.2017.11.219; PMID 29197793) owns its Pilbara reconstructed-soil/Triodia/Acacia observations. DASHI owns only the typed separations among inoculum viability, indigenous propagules, colonisation, soil function, recruitment and survival."
