module DASHI.Biology.Agriculture.AustralianGrassDiazotrophNitrogenExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Environment.LESResearchCrossPollinationExact as LES
import DASHI.Biology.Agriculture.NitrogenaseChemistryCrossPollinationExact as Chemistry

------------------------------------------------------------------------
-- AUSTRALIAN GRASS-ASSOCIATED / ENDOPHYTIC DIAZOTROPHY
--
-- This owner gives a fourth biological N-input mechanism distinct from
-- legume-rhizobium, Casuarina-Frankia and biocrust community diazotrophy.
-- Australian perennial-grass evidence and Sorghum-bicolor mucilage evidence
-- remain separate empirical objects.
------------------------------------------------------------------------

guptaEtAl2019DOI : String
guptaEtAl2019DOI = "10.3389/fmolb.2019.00115"

guptaEtAl2019PMID : String
guptaEtAl2019PMID = "31750314"

guptaEtAl2019PMCID : String
guptaEtAl2019PMCID = "PMC6848460"

venadoEtAl2025DOI : String
venadoEtAl2025DOI = "10.1371/journal.pbio.3003037"

venadoEtAl2025PMID : String
venadoEtAl2025PMID = "40029899"

venadoEtAl2025PMCID : String
venadoEtAl2025PMCID = "PMC12136154"

guptaEtAl2019 : Attribution.AttributedSource
guptaEtAl2019 = Attribution.mkDOISource
  "Vadakattu V. S. R. Gupta; Bangzhou Zhang; Christopher Ryan Penton; Julian Yu; James M. Tiedje"
  "Diazotroph Diversity and Nitrogen Fixation in Summer Active Perennial Grasses in a Mediterranean Region Agricultural Soil"
  "Frontiers in Molecular Biosciences 6:115"
  "2019"
  guptaEtAl2019DOI
  "https://pubmed.ncbi.nlm.nih.gov/31750314/"
  Attribution.academicArticleSource
  "Australian field-grown unfertilised summer-active perennial grasses (Panicum coloratum, Chloris gayana and Digitaria eriantha) were analysed using nifH amplicon sequencing/qPCR and 15N-enriched incubation assays. Diazotrophic communities occurred in above- and below-ground plant compartments and fixation potentials varied by species/compartment. The study does not quantify a whole-year field contribution to plant N demand or fertilizer replacement."
  Attribution.publicAttribution

venadoEtAl2025 : Attribution.AttributedSource
venadoEtAl2025 = Attribution.mkDOISource
  "Rafael E. Venado; Jennifer Wilker; Vania C. S. Pankievicz; Valentina Infante; April MacIntyre; Emily S. A. Wolf; Saddie Vela; Fletcher Robbins; Paulo Ivan Fernandes-Junior; Wilfred Vermerris; Jean-Michel Ane"
  "Mucilage produced by aerial roots hosts diazotrophs that provide nitrogen in Sorghum bicolor"
  "PLOS Biology 23(3):e3003037"
  "2025"
  venadoEtAl2025DOI
  "https://pubmed.ncbi.nlm.nih.gov/40029899/"
  Attribution.academicArticleSource
  "Sorghum-bicolor study combining field observations, acetylene reduction, 15N2 gas feeding and 15N isotope dilution. Aerial-root mucilage-associated diazotrophs supplied substantial atmospheric N in selected sorghum accessions under controlled experiments, with aerial-root/mucilage development strongly genotype- and environment-dependent. This is not Sorghum-sudanense/sudangrass same-object evidence."
  Attribution.publicAttribution

------------------------------------------------------------------------
-- Evidence roles.
------------------------------------------------------------------------

data GrassDiazotrophEvidenceRole : Set where
  AustralianPerennialGrassDiazotrophPotential : GrassDiazotrophEvidenceRole
  SorghumMucilageDirectBNF : GrassDiazotrophEvidenceRole

record GrassDiazotrophReceipt : Set where
  constructor grass-diazotroph-receipt
  field
    source : Attribution.AttributedSource
    sourceDOI : String
    role : GrassDiazotrophEvidenceRole
    hostReading : String
    compartmentReading : String
    methodReading : String
    boundedReading : String
open GrassDiazotrophReceipt public

australianGrassReceipt : GrassDiazotrophReceipt
australianGrassReceipt = grass-diazotroph-receipt
  guptaEtAl2019
  guptaEtAl2019DOI
  AustralianPerennialGrassDiazotrophPotential
  "field-grown unfertilised Panicum coloratum, Chloris gayana and Digitaria eriantha in South Australian agricultural soil"
  "roots, stems/leaves and associated endophytic/rhizosphere diazotroph niches"
  "nifH sequencing/qPCR plus 15N-enriched in-vitro functional assay"
  "presence/abundance and fixation potential are retained separately from annual field N contribution to host demand"

sorghumMucilageReceipt : GrassDiazotrophReceipt
sorghumMucilageReceipt = grass-diazotroph-receipt
  venadoEtAl2025
  venadoEtAl2025DOI
  SorghumMucilageDirectBNF
  "selected Sorghum bicolor accessions"
  "aerial-root carbohydrate-rich mucilage microbiome"
  "field trait observation plus ARA, 15N2 gas feeding and 15N isotope dilution"
  "direct BNF/plant-N evidence is genotype/environment indexed and does not transfer to sudangrass or Australian perennial grass same objects"

------------------------------------------------------------------------
-- Functional N-input role != mechanism.
------------------------------------------------------------------------

data BiologicalNInputSystem : Set where
  legumeRhizobiumSystem : BiologicalNInputSystem
  actinorhizalFrankiaSystem : BiologicalNInputSystem
  biocrustDiazotrophSystem : BiologicalNInputSystem
  grassAssociatedDiazotrophSystem : BiologicalNInputSystem

data BiologicalNInputRole : Set where
  biologicalNInputRole : BiologicalNInputRole

data NInputMechanism : Set where
  legumeNoduleMechanism : NInputMechanism
  actinorhizalNoduleMechanism : NInputMechanism
  biocrustCommunityMechanism : NInputMechanism
  grassEndosphereMucilageMechanism : NInputMechanism

nInputRole : BiologicalNInputSystem → BiologicalNInputRole
nInputRole _ = biologicalNInputRole

nInputMechanism : BiologicalNInputSystem → NInputMechanism
nInputMechanism legumeRhizobiumSystem = legumeNoduleMechanism
nInputMechanism actinorhizalFrankiaSystem = actinorhizalNoduleMechanism
nInputMechanism biocrustDiazotrophSystem = biocrustCommunityMechanism
nInputMechanism grassAssociatedDiazotrophSystem = grassEndosphereMucilageMechanism

sameRoleDoesNotIdentifyMechanism :
  nInputMechanism legumeRhizobiumSystem ≡
  nInputMechanism grassAssociatedDiazotrophSystem → ⊥
sameRoleDoesNotIdentifyMechanism ()

------------------------------------------------------------------------
-- Information-loss witness: nifH abundance alone cannot answer plant-N
-- contribution because realised function and transfer remain context indexed.
------------------------------------------------------------------------

data GrassWorld : Set where
  sameNifHLowPlantContribution : GrassWorld
  sameNifHHighPlantContribution : GrassWorld

data GrassTask : Set where
  plantNContributionTask : GrassTask

data NifHToken : Set where
  nifHPresent : NifHToken

nifHOnly : GrassWorld → NifHToken
nifHOnly _ = nifHPresent

plantNContribution : GrassTask → GrassWorld → Bool
plantNContribution plantNContributionTask sameNifHLowPlantContribution = false
plantNContribution plantNContributionTask sameNifHHighPlantContribution = true

trueNotFalse : true ≡ false → ⊥
trueNotFalse ()

nifHNotTaskSufficientForPlantContribution :
  LES.TaskFactorisation nifHOnly plantNContribution → ⊥
nifHNotTaskSufficientForPlantContribution factor =
  trueNotFalse
    (LES.sameRepresentationSameTaskOutput
      factor plantNContributionTask
      {sameNifHHighPlantContribution} {sameNifHLowPlantContribution} refl)

------------------------------------------------------------------------
-- Canonical ladder remains untouched.
------------------------------------------------------------------------

bacterialFixedNFluxStillOpen :
  Chemistry.stageClosed Chemistry.bacterialFixedNFlux ≡ false
bacterialFixedNFluxStillOpen = refl

avoidedMineralNStillOpen :
  Chemistry.stageClosed Chemistry.avoidedMineralN ≡ false
avoidedMineralNStillOpen = refl

------------------------------------------------------------------------
-- No-promotion boundary.
------------------------------------------------------------------------

record GrassDiazotrophBoundary : Set where
  constructor grass-diazotroph-boundary
  field
    sameBiologicalNInputRoleImpliesSameMechanism : Bool
    nifHAbundanceImpliesPlantNitrogenContribution : Bool
    inVitroFixationPotentialImpliesAnnualFieldNContribution : Bool
    plantCompartmentMayBeDropped : Bool
    hostSpeciesMayBeDropped : Bool
    environmentAndGenotypeMayBeDropped : Bool
    sorghumBicolorMucilageCreatesSudangrassSameObjectEvidence : Bool
    sorghumNdfaCreatesAvoidedMineralNReceipt : Bool
    perennialGrassPotentialClosesSeasonalCropNDemand : Bool
    associativeDiazotrophyCreatesDeploymentAuthority : Bool
    sourceMeasurementsAreSyntheticDASHIWorlds : Bool
open GrassDiazotrophBoundary public

canonicalGrassDiazotrophBoundary : GrassDiazotrophBoundary
canonicalGrassDiazotrophBoundary = grass-diazotroph-boundary
  false false false false false false false false false false false

attributionRule : String
attributionRule =
  "Gupta et al. 2019 (DOI 10.3389/fmolb.2019.00115; PMID 31750314; PMCID PMC6848460) owns its Australian field-grown perennial-grass nifH-community and 15N-incubation fixation-potential propositions. Venado et al. 2025 (DOI 10.1371/journal.pbio.3003037; PMID 40029899; PMCID PMC12136154) owns its Sorghum-bicolor aerial-root mucilage/diazotroph and isotope-based plant-N propositions. DASHI owns only the mechanism-independent biological-N-input abstraction, synthetic nifH-information-loss witness and no-promotion boundary. Australian perennial grasses, Sorghum bicolor and Sorghum-sudanense/sudangrass remain distinct empirical objects; none of these sources silently closes generic seasonal crop-N demand or avoided mineral N."
