module DASHI.Biology.Agriculture.AustralianBiocrustNitrogenRestorationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Environment.LESResearchCrossPollinationExact as LES
import DASHI.Biology.Agriculture.NitrogenaseChemistryCrossPollinationExact as Chemistry

------------------------------------------------------------------------
-- AUSTRALIAN BIOCRUST NITROGEN / DRYLAND RESTORATION
--
-- Biological soil crusts provide an independent, non-vascular instance of
-- a nitrogen-input / pioneer-recovery role.  Presence of N-fixing taxa or
-- genes, biocrust cover, and soil C recovery remain distinct from directly
-- measured N2-fixation flux and from plant-available or crop-demand N.
------------------------------------------------------------------------

munozRojasEtAl2018DOI : String
munozRojasEtAl2018DOI = "10.1016/j.scitotenv.2018.04.265"

munozRojasEtAl2018PMID : String
munozRojasEtAl2018PMID = "29913577"

chuaEtAl2020DOI : String
chuaEtAl2020DOI = "10.1111/rec.13040"

williamsEtAl2022DOI : String
williamsEtAl2022DOI = "10.3390/agronomy12010062"

cofreEtAl2026DOI : String
cofreEtAl2026DOI = "10.1007/s00374-025-01963-9"

munozRojasEtAl2018 : Attribution.AttributedSource
munozRojasEtAl2018 = Attribution.mkDOISource
  "Miriam Munoz-Rojas; J. R. Roman; Beatriz Roncero-Ramos; Todd E. Erickson; David J. Merritt; P. Aguila-Carricondo; Yolanda Canton"
  "Cyanobacteria inoculation enhances carbon sequestration in soil substrates used in dryland restoration"
  "Science of the Total Environment 636:1149-1154"
  "2018"
  munozRojasEtAl2018DOI
  "https://pubmed.ncbi.nlm.nih.gov/29913577/"
  Attribution.academicArticleSource
  "Pilbara post-mine dryland-restoration microcosm using a consortium of N-fixing cyanobacteria on stockpiled topsoil, mine waste and mixed substrates. Inoculation rapidly increased biocrust cover and soil organic carbon. The experiment supports biocrust establishment and soil-C-function recovery, not a directly measured ecosystem N2-fixation flux or plant-N-demand receipt."
  Attribution.publicAttribution

chuaEtAl2020 : Attribution.AttributedSource
chuaEtAl2020 = Attribution.mkDOISource
  "Melissa Chua; Todd E. Erickson; David J. Merritt; Angela M. Chilton; Mark K. J. Ooi; Miriam Munoz-Rojas"
  "Bio-priming seeds with cyanobacteria: effects on native plant growth and soil properties"
  "Restoration Ecology 28(S2):S168-S176"
  "2020"
  chuaEtAl2020DOI
  "https://doi.org/10.1111/rec.13040"
  Attribution.academicArticleSource
  "Western Australian dryland mine-restoration laboratory/glasshouse study using indigenous cyanobacterial seed bio-priming across native species and mine substrates. Some species showed longer roots or shoots, but responses were species- and substrate-specific. Early germination/seedling responses are not promoted to field trajectory recovery."
  Attribution.publicAttribution

williamsEtAl2022 : Attribution.AttributedSource
williamsEtAl2022 = Attribution.mkDOISource
  "Wendy J. Williams; Susanne Schmidt; Eli Zaady; Bruce Alchin; Than Myint Swe; Stephen Williams; Madeline Dooley; Grace Penfold; Peter O'Reagain; John Bushell; Robyn Cowley; Colin Driscoll; Nicole Robinson"
  "Resting Subtropical Grasslands from Grazing in the Wet Season Boosts Biocrust Hotspots to Improve Soil Health"
  "Agronomy 12(1):62"
  "2022"
  williamsEtAl2022DOI
  "https://doi.org/10.3390/agronomy12010062"
  Attribution.academicArticleSource
  "Long-term north-eastern Australian grazing-management study comparing soil type, stocking rate and wet-season spelling. Rotational spelling with moderate stocking retained more biocrust cover; cyanobacteria dominated biocrusts. The source supports grazing/season/soil control of biocrust state, not a universal management ranking or direct fertilizer-substitution quantity."
  Attribution.publicAttribution

cofreEtAl2026 : Attribution.AttributedSource
cofreEtAl2026 = Attribution.mkDOISource
  "M. V. Cofre; J. Sun; W. Williams; R. Lyons; P. O'Reagain; S. Schmidt; P. G. Dennis"
  "Impacts of grazing management on biocrust microbiomes and their potential to input and cycle nutrients"
  "Biology and Fertility of Soils 62(1):139-153"
  "2026"
  cofreEtAl2026DOI
  "https://doi.org/10.1007/s00374-025-01963-9"
  Attribution.academicArticleSource
  "Australian rangeland biocrust microbiome study retaining grazing management, composition and nutrient-cycling potential. N-fixation-capable lineages/genes and their management sensitivity are treated as potential/indicator evidence; gene frequency is not identified with measured landscape N2-fixation flux."
  Attribution.publicAttribution

------------------------------------------------------------------------
-- Evidence roles.
------------------------------------------------------------------------

data BiocrustEvidenceRole : Set where
  inoculatedBiocrustEstablishment : BiocrustEvidenceRole
  nativeSeedBioPriming : BiocrustEvidenceRole
  grazingBiocrustManagement : BiocrustEvidenceRole
  microbiomeNFixationPotential : BiocrustEvidenceRole

record BiocrustReceipt : Set where
  constructor biocrust-receipt
  field
    source : Attribution.AttributedSource
    sourceDOI : String
    role : BiocrustEvidenceRole
    organismalReading : String
    spatialReading : String
    managementReading : String
    measuredReading : String
open BiocrustReceipt public

pilbaraBiocrustReceipt : BiocrustReceipt
pilbaraBiocrustReceipt = biocrust-receipt
  munozRojasEtAl2018
  munozRojasEtAl2018DOI
  inoculatedBiocrustEstablishment
  "N-fixing cyanobacterial consortium forming biological soil crust"
  "Pilbara reconstructed mine substrates in controlled microcosms"
  "cyanobacterial inoculation versus substrate controls"
  "biocrust cover, chlorophyll-a, soil organic C and C mineralisation; not direct N2 flux"

seedBioPrimingReceipt : BiocrustReceipt
seedBioPrimingReceipt = biocrust-receipt
  chuaEtAl2020
  chuaEtAl2020DOI
  nativeSeedBioPriming
  "indigenous Pilbara cyanobacterial inoculant plus native plant seeds"
  "laboratory/glasshouse; topsoil and mine-waste substrates"
  "seed bio-priming"
  "species-specific germination/root/shoot responses and soil-function variables; not field recovery trajectory"

queenslandBiocrustManagementReceipt : BiocrustReceipt
queenslandBiocrustManagementReceipt = biocrust-receipt
  williamsEtAl2022
  williamsEtAl2022DOI
  grazingBiocrustManagement
  "cyanobacteria-dominated rangeland biocrust"
  "grass-tussock/interspace hotspots across two soil types"
  "stocking rate crossed with wet-season rotational spelling"
  "biocrust cover/soil-health state; management and rainfall/soil context retained"

biocrustGenePotentialReceipt : BiocrustReceipt
biocrustGenePotentialReceipt = biocrust-receipt
  cofreEtAl2026
  cofreEtAl2026DOI
  microbiomeNFixationPotential
  "biocrust bacterial community including potentially N-fixing lineages"
  "Australian rangeland biocrust samples"
  "grazing management and seasonal context"
  "microbiome composition and N-fixation-gene potential; not direct landscape N2 flux"

------------------------------------------------------------------------
-- N-fixing role != vascularity or one mechanism.
------------------------------------------------------------------------

data NInputPioneer : Set where
  vascularPioneer : NInputPioneer
  biocrustPioneer : NInputPioneer

data OrganismalLevel : Set where
  vascularPlantLevel : OrganismalLevel
  microbialCommunityLevel : OrganismalLevel

data NitrogenInputRole : Set where
  biologicalNitrogenInput : NitrogenInputRole

nInputRole : NInputPioneer → NitrogenInputRole
nInputRole _ = biologicalNitrogenInput

organismalLevel : NInputPioneer → OrganismalLevel
organismalLevel vascularPioneer = vascularPlantLevel
organismalLevel biocrustPioneer = microbialCommunityLevel

sameRoleDoesNotIdentifyOrganismalLevel :
  organismalLevel vascularPioneer ≡ organismalLevel biocrustPioneer → ⊥
sameRoleDoesNotIdentifyOrganismalLevel ()

------------------------------------------------------------------------
-- Measurement information-loss witness: gene/cover projection cannot answer
-- a direct-flux consumer in general.
------------------------------------------------------------------------

data BiocrustWorld : Set where
  sameIndicatorLowRealisedFlux : BiocrustWorld
  sameIndicatorHighRealisedFlux : BiocrustWorld

data BiocrustTask : Set where
  measuredNFluxTask : BiocrustTask

data IndicatorToken : Set where
  nFixationPotentialPresent : IndicatorToken

indicatorOnly : BiocrustWorld → IndicatorToken
indicatorOnly _ = nFixationPotentialPresent

measuredNFluxAdequate : BiocrustTask → BiocrustWorld → Bool
measuredNFluxAdequate measuredNFluxTask sameIndicatorLowRealisedFlux = false
measuredNFluxAdequate measuredNFluxTask sameIndicatorHighRealisedFlux = true

trueNotFalse : true ≡ false → ⊥
trueNotFalse ()

indicatorNotTaskSufficientForMeasuredFlux :
  LES.TaskFactorisation indicatorOnly measuredNFluxAdequate → ⊥
indicatorNotTaskSufficientForMeasuredFlux factor =
  trueNotFalse
    (LES.sameRepresentationSameTaskOutput
      factor measuredNFluxTask
      {sameIndicatorHighRealisedFlux} {sameIndicatorLowRealisedFlux} refl)

------------------------------------------------------------------------
-- Canonical BNF ladder remains authoritative.
------------------------------------------------------------------------

acaciaBacterialFixedNFluxStillOpen :
  Chemistry.stageClosed Chemistry.bacterialFixedNFlux ≡ false
acaciaBacterialFixedNFluxStillOpen = refl

------------------------------------------------------------------------
-- No-promotion boundary.
------------------------------------------------------------------------

record BiocrustBoundary : Set where
  constructor biocrust-boundary
  field
    nFixingPioneerRoleImpliesVascularPlant : Bool
    biocrustCoverImpliesMeasuredNFixationFlux : Bool
    nFixationGeneFrequencyImpliesMeasuredNFixationFlux : Bool
    NFixingTaxonPresenceImpliesMeasuredNFixationFlux : Bool
    soilCarbonGainImpliesPlantAvailableNitrogen : Bool
    soilCarbonGainImpliesNativeCommunityRecovery : Bool
    bioPrimingSeedlingResponseImpliesFieldTrajectoryRecovery : Bool
    fireGrazingSeasonSoilMayBeDropped : Bool
    biocrustNitrogenInputImpliesCropDemandSatisfaction : Bool
    biocrustEvidenceClosesAcaciaBacterialFixedNFlux : Bool
    biocrustEvidenceCreatesAvoidedMineralNReceipt : Bool
    sourceMeasurementsAreSyntheticDASHIWorlds : Bool
open BiocrustBoundary public

canonicalBiocrustBoundary : BiocrustBoundary
canonicalBiocrustBoundary = biocrust-boundary
  false false false false false false false false false false false false

attributionRule : String
attributionRule =
  "Munoz-Rojas et al. 2018 (DOI 10.1016/j.scitotenv.2018.04.265; PMID 29913577) owns its Pilbara cyanobacterial-inoculation/biocrust/soil-carbon propositions. Chua et al. 2020 (DOI 10.1111/rec.13040) owns its indigenous-cyanobacteria seed-bio-priming and species/substrate-specific seedling propositions. Williams et al. 2022 (DOI 10.3390/agronomy12010062) owns its Australian grazing/spelling/soil-type biocrust observations. Cofre et al. 2026 (DOI 10.1007/s00374-025-01963-9) owns its grazing-management biocrust microbiome and N-fixation-potential propositions. DASHI owns the non-vascular N-input-role abstraction, synthetic information-loss witness and no-promotion boundary. Presence of cyanobacteria, N-fixation genes, biocrust cover or soil-C improvement is not relabelled as measured N2 flux, crop-N-demand satisfaction, avoided mineral N or Acacia/Senegalia same-object evidence."
