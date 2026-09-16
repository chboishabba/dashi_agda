module DASHI.ComputerScience.FlyPesticideSourceAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity

------------------------------------------------------------------------
-- DROSOPHILA PESTICIDE / ENVIRONMENTAL-TOXICOLOGY SOURCE ATLAS
--
-- This is an acquisition/indexing owner, not a toxicology theory.  Each paper
-- retains publication identity and its own source-bounded endpoint role.
-- DOI/PMID/PMCID/QID/taxon identifiers navigate provenance; they do not create
-- biological truth, causal mechanism, consumer adequacy, or cross-study identity.
------------------------------------------------------------------------

data FlyToxicologyRole : Set where
  neuralMemoryCircadianRole
  neuralSynapticMemoryRole
  reproductiveOvaryRole
  reproductiveStemCellRole
  multiPesticideLifeHistoryRole
  genotoxicDNARepairRole
  resistanceBehaviourRole
  chlorpyrifosMultigenerationRole : FlyToxicologyRole

record FlyPesticideStudy : Set where
  constructor fly-pesticide-study
  field
    label : String
    source : Attribution.AttributedSource
    role : FlyToxicologyRole
    pmid : String
    pmcid : String
    articleQid : Identity.ExternalIdentityDemand
    exposureIdentity : String
    observationDefinition : String
    sourceBoundedFinding : String
    nonPromotion : String
open FlyPesticideStudy public

mkArticleQidDemand : String → String → Identity.ExternalIdentityDemand
mkArticleQidDemand label title =
  Identity.mkOptionalIdentityDemand
    "Fly pesticide SOTA source atlas"
    label
    title
    Identity.wikidataQid
    (Identity.unresolved "article-level Wikidata QID not independently verified")

------------------------------------------------------------------------
-- Organism identity is independent of each experimental manifestation.
------------------------------------------------------------------------

drosophilaMelanogasterQid : Identity.ExternalIdentityDemand
drosophilaMelanogasterQid =
  Identity.mkOptionalIdentityDemand
    "Fly pesticide SOTA source atlas"
    "Drosophila melanogaster taxon identity"
    "Drosophila melanogaster"
    Identity.wikidataQid
    (Identity.verified "Wikidata" "Q130888")

drosophilaNcbiTaxon : Identity.ExternalIdentityDemand
drosophilaNcbiTaxon =
  Identity.mkOptionalIdentityDemand
    "Fly pesticide SOTA source atlas"
    "Drosophila melanogaster NCBI taxonomy identity"
    "Drosophila melanogaster"
    Identity.officialIdentifier
    (Identity.verified "NCBI Taxonomy" "7227")

------------------------------------------------------------------------
-- CNS / neural-observer sources.
------------------------------------------------------------------------

tasman2021 : FlyPesticideStudy
tasman2021 =
  fly-pesticide-study
    "Tasman et al. 2021 neonicotinoid memory/circadian study"
    (Attribution.mkDOISource
      "Tasman, Hidalgo, Zhu, Rands and Hodge"
      "Neonicotinoids disrupt memory, circadian behaviour and sleep"
      "Scientific Reports"
      "2021"
      "10.1038/s41598-021-81548-2"
      "https://pmc.ncbi.nlm.nih.gov/articles/PMC7820356/"
      Attribution.academicArticleSource
      "pays only the paper's Drosophila neonicotinoid memory/circadian/sleep observations and declared neural manipulations"
      Attribution.publicAttribution)
    neuralMemoryCircadianRole
    "33479461"
    "PMC7820356"
    (mkArticleQidDemand "Tasman 2021 article QID" "Neonicotinoids disrupt memory, circadian behaviour and sleep")
    "imidacloprid / clothianidin / thiamethoxam / thiacloprid exposures, with concentration and developmental timing as defined by source"
    "olfactory memory, locomotion, circadian rhythm/sleep, clock-neuron PDF and nAChR-subunit perturbation"
    "field-relevant neonicotinoid exposures produced endpoint-specific memory/circadian/sleep effects; source distinguishes compounds and endpoints"
    "does not establish a universal pesticide-CNS mechanism or transfer results to every insecticide"

schulz2024 : FlyPesticideStudy
schulz2024 =
  fly-pesticide-study
    "Schulz et al. 2024 imidacloprid memory/synaptic study"
    (Attribution.mkDOISource
      "Schulz, Franz, Deimel and Widmann"
      "Exploring neonicotinoid effects on Drosophila: insights into olfactory memory, neurotransmission, and synaptic connectivity"
      "Frontiers in Physiology"
      "2024"
      "10.3389/fphys.2024.1363943"
      "https://pmc.ncbi.nlm.nih.gov/articles/PMC10973132/"
      Attribution.academicArticleSource
      "pays only the paper's imidacloprid exposure-stage/concentration and memory/synaptic observations"
      Attribution.publicAttribution)
    neuralSynapticMemoryRole
    "38550256"
    "PMC10973132"
    (mkArticleQidDemand "Schulz 2024 article QID" "Exploring neonicotinoid effects on Drosophila")
    "imidacloprid exposure with larval-versus-adult timing and source-defined concentrations"
    "3-min and 24-h olfactory memory plus neurotransmission/synaptic-connectivity readouts"
    "memory impairment depends on developmental stage, concentration, and memory-timescale observer"
    "same chemical identity does not collapse exposure window or short-/long-term memory into one observer"

------------------------------------------------------------------------
-- Reproduction / development sources.
------------------------------------------------------------------------

muller2021Roundup : FlyPesticideStudy
muller2021Roundup =
  fly-pesticide-study
    "Muller et al. 2021 Roundup reproduction study"
    (Attribution.mkDOISource
      "Muller, Herrera, Talyn and Melchiorre"
      "Toxicological Effects of Roundup on Drosophila melanogaster Reproduction"
      "Toxics"
      "2021"
      "10.3390/toxics9070161"
      "https://pmc.ncbi.nlm.nih.gov/articles/PMC8309847/"
      Attribution.academicArticleSource
      "pays source-bounded formulation/exposure-window effects on ovary volume, mature oocytes and related reproductive observations"
      Attribution.publicAttribution)
    reproductiveOvaryRole
    "34357904"
    "PMC8309847"
    (mkArticleQidDemand "Muller 2021 article QID" "Toxicological Effects of Roundup on Drosophila melanogaster Reproduction")
    "Roundup Ready to Use / Super Concentrate formulations at source-defined sublethal concentrations and post-eclosion windows"
    "female body size, ovary volume, mature-oocyte count and reproductive anatomy"
    "formulation and early post-eclosion exposure context alter reproductive endpoints; formulation cannot be erased to glyphosate token alone"
    "does not identify every formulation effect with glyphosate active ingredient alone"

sun2026Thiacloprid : FlyPesticideStudy
sun2026Thiacloprid =
  fly-pesticide-study
    "Sun et al. 2026 thiacloprid fecundity study"
    (Attribution.mkDOISource
      "Sun, Liu, Lv and Zhong"
      "Neurotoxic pesticide thiacloprid impairs Drosophila fecundity by disrupting germline stem cell differentiation and somatic cell apoptosis in ovary"
      "Pesticide Biochemistry and Physiology"
      "2026"
      "10.1016/j.pestbp.2025.106811"
      "https://pubmed.ncbi.nlm.nih.gov/41350065/"
      Attribution.academicArticleSource
      "pays source-bounded thiacloprid developmental/reproductive observations and the reported dpp/bam/GSC/escort-cell mechanism evidence"
      Attribution.publicAttribution)
    reproductiveStemCellRole
    "41350065"
    "PMCID unresolved in inspected sources"
    (mkArticleQidDemand "Sun 2026 article QID" "Neurotoxic pesticide thiacloprid impairs Drosophila fecundity")
    "thiacloprid at source-defined sublethal concentrations"
    "larval development, ovary/testis residue, GSC differentiation, somatic-cell apoptosis, oviposition and sperm counts"
    "paper reports premature GSC differentiation associated with dpp downregulation/bam upregulation and escort-cell apoptosis"
    "does not make all neonicotinoid reproductive mechanisms identical"

kishore2026Mixture : FlyPesticideStudy
kishore2026Mixture =
  fly-pesticide-study
    "Kishore et al. 2026 real-world pesticide panel and mixture study"
    (Attribution.mkDOISource
      "Kishore et al."
      "Impact of agricultural pesticides on survival, behavior, and reproductive capacity in Drosophila melanogaster at real-world exposure levels"
      "Journal of Environmental Management"
      "2026"
      "10.1016/j.jenvman.2025.128324"
      "https://pubmed.ncbi.nlm.nih.gov/41418506/"
      Attribution.academicArticleSource
      "pays the study's source-defined pesticide-panel, formulation/mixture, survival, locomotion and reproduction observations"
      Attribution.publicAttribution)
    multiPesticideLifeHistoryRole
    "41418506"
    "PMCID unresolved in inspected sources"
    (mkArticleQidDemand "Kishore 2026 article QID" "Impact of agricultural pesticides on survival, behavior, and reproductive capacity in Drosophila melanogaster at real-world exposure levels")
    "11-pesticide panel, Roundup Exel formulation and source-defined mixture at LOQ/MRL-related exposure levels"
    "survival, locomotion, reproductive capacity and F2/F1 continuity"
    "several pesticides/formulations/mixtures produced distinct endpoint patterns; mixture/formulation effects are not reducible to one active-ingredient token"
    "reported synergy/combined toxicity is study-design-specific and not a universal mixture law"

------------------------------------------------------------------------
-- DNA/genotoxic and genotype/behaviour sources.
------------------------------------------------------------------------

mishra2014Dichlorvos : FlyPesticideStudy
mishra2014Dichlorvos =
  fly-pesticide-study
    "Mishra et al. 2014 dichlorvos DNA-repair study"
    (Attribution.mkDOISource
      "Mishra, Sharma, Shukla, Kumar, Dwivedi and Kar Chowdhuri"
      "Genotoxicity of dichlorvos in strains of Drosophila melanogaster defective in DNA repair"
      "Mutation Research Genetic Toxicology and Environmental Mutagenesis"
      "2014"
      "10.1016/j.mrgentox.2014.02.004"
      "https://pubmed.ncbi.nlm.nih.gov/24614193/"
      Attribution.academicArticleSource
      "pays source-bounded in-vivo dichlorvos/comet-assay observations across declared DNA-repair and oxidative-stress genotypes"
      Attribution.publicAttribution)
    genotoxicDNARepairRole
    "24614193"
    "PMCID unresolved in inspected sources"
    (mkArticleQidDemand "Mishra 2014 article QID" "Genotoxicity of dichlorvos in strains of Drosophila melanogaster defective in DNA repair")
    "dichlorvos exposure at source-defined environmentally relevant concentrations and 48-h duration"
    "midgut-cell comet assay across wild type and pre-/post-replication DNA-repair or oxidative-stress mutants"
    "DNA-damage response differs by dose and repair genotype; oxidative DNA damage and repair pathway status remain live coordinates"
    "same pesticide dose does not determine DNA damage independently of genotype/assay/tissue"

nogueiraAlves2026 : FlyPesticideStudy
nogueiraAlves2026 =
  fly-pesticide-study
    "Nogueira Alves et al. 2026 Cyp6g1 oviposition/resistance study"
    (Attribution.mkDOISource
      "Nogueira Alves et al."
      "Insecticide Resistance Alters Oviposition Preference in Drosophila melanogaster"
      "Ecology and Evolution"
      "2026"
      "10.1002/ece3.73067"
      "https://pmc.ncbi.nlm.nih.gov/articles/PMC12884133/"
      Attribution.academicArticleSource
      "pays source-bounded Cyp6g1 genotype, insecticide-choice, oviposition and life-stage survival observations"
      Attribution.publicAttribution)
    resistanceBehaviourRole
    "41668992"
    "PMC12884133"
    (mkArticleQidDemand "Nogueira Alves 2026 article QID" "Insecticide Resistance Alters Oviposition Preference in Drosophila melanogaster")
    "DDT / imidacloprid / spinosad choice environments with source-defined Cyp6g1 alleles"
    "oviposition preference plus larval/adult survival under matching exposure conditions"
    "resistance genotype is associated with context-dependent oviposition behaviour and compound-specific survival consequences"
    "resistance allele does not imply generic avoidance or universal cross-protection"

------------------------------------------------------------------------
-- Canonical source-role receipts: source ownership stays with each paper.
------------------------------------------------------------------------

tasmanReceipt : Snowball.SourceRoleSnowballReceipt (source tasman2021)
tasmanReceipt = Snowball.canonicalSourceRoleSnowballReceipt (source tasman2021)

mullerReceipt : Snowball.SourceRoleSnowballReceipt (source muller2021Roundup)
mullerReceipt = Snowball.canonicalSourceRoleSnowballReceipt (source muller2021Roundup)

mishraReceipt : Snowball.SourceRoleSnowballReceipt (source mishra2014Dichlorvos)
mishraReceipt = Snowball.canonicalSourceRoleSnowballReceipt (source mishra2014Dichlorvos)

------------------------------------------------------------------------
-- WrongType / attribution firewalls.
------------------------------------------------------------------------

data SamePesticideImpliesSameEndpoint : Set where
data SameSpeciesImpliesSameExperimentalObject : Set where
data QidCreatesToxicologyAuthority : Set where
data CitationImportsMechanism : Set where

data SameEndpointNameImpliesSameMeasurementDefinition : Set where

samePesticideDoesNotCreateSameEndpoint : SamePesticideImpliesSameEndpoint → ⊥
samePesticideDoesNotCreateSameEndpoint ()

sameSpeciesDoesNotCreateSameExperimentalObject : SameSpeciesImpliesSameExperimentalObject → ⊥
sameSpeciesDoesNotCreateSameExperimentalObject ()

qidDoesNotCreateToxicologyAuthority : QidCreatesToxicologyAuthority → ⊥
qidDoesNotCreateToxicologyAuthority ()

citationDoesNotImportMechanism : CitationImportsMechanism → ⊥
citationDoesNotImportMechanism ()

sameEndpointNameDoesNotCreateSameMeasurementDefinition :
  SameEndpointNameImpliesSameMeasurementDefinition → ⊥
sameEndpointNameDoesNotCreateSameMeasurementDefinition ()

record FlyPesticideSourceAtlas : Set where
  constructor fly-pesticide-source-atlas
  field
    organismIdentityPaid : Bool
    publicationIdentitiesRetained : Bool
    neuralObservationFamilyPaid : Bool
    reproductiveObservationFamilyPaid : Bool
    genotoxicObservationFamilyPaid : Bool
    mixtureEnvironmentalFamilyPaid : Bool
    resistanceBehaviourFamilyPaid : Bool
    articleQidsMayRemainUnresolved : Bool
    citationCreatesToxicologyAuthority : Bool
    samePesticideCreatesSameEndpoint : Bool
    sameSpeciesCreatesSameExperimentalObject : Bool
    sourceAtlasReading : String
open FlyPesticideSourceAtlas public

canonicalFlyPesticideSourceAtlas : FlyPesticideSourceAtlas
canonicalFlyPesticideSourceAtlas =
  fly-pesticide-source-atlas
    true true true true true true true true
    false false false
    "multi-source Drosophila pesticide SOTA atlas: publication/taxon identifiers and source roles retained independently; toxicology claims remain study-, exposure-, assay-, tissue-, genotype- and endpoint-bounded"
