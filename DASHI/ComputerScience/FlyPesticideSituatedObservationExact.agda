module DASHI.ComputerScience.FlyPesticideSituatedObservationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.ComputerScience.FlyStructureFunctionNDimFibreExact as FlyNDim
import DASHI.ComputerScience.FlyPesticideSourceAtlasExact as Atlas
import DASHI.Wikimedia.IbrahimPesticideExperimentDesignParetoExact as Experiment

------------------------------------------------------------------------
-- SITUATED DROSOPHILA PESTICIDE OBSERVATION
--
-- This owner backpropagates the acquisition/observer/provenance discipline from
-- the protein/AdK programme into the mature Fly NDim lane.  The biology remains
-- source-owned by the individual papers in FlyPesticideSourceAtlasExact.  The
-- finite collisions, projection defects and repaired carrier below are DASHI
-- synthesis.
--
-- A pesticide observation is not a bare chemical name or endpoint number.  It
-- retains exposure, organism/genotype/life-stage context, tissue/region,
-- measurement definition, source role and locator.  Connectome fibre identity
-- remains an independent optional structural coordinate and cannot manufacture
-- a toxicology mechanism.
------------------------------------------------------------------------

data PesticideIdentity : Set where
  thiaclopridIdentity : PesticideIdentity
  imidaclopridIdentity : PesticideIdentity
  dichlorvosIdentity : PesticideIdentity
  roundupFormulationIdentity : PesticideIdentity
  pesticideMixtureIdentity : PesticideIdentity

data ObservationFamily : Set where
  neuralBehaviourObservation : ObservationFamily
  reproductiveObservation : ObservationFamily
  genotoxicObservation : ObservationFamily
  lifeHistoryObservation : ObservationFamily

data LifeStageWindow : Set where
  larvalWindow : LifeStageWindow
  adultWindow : LifeStageWindow
  earlyPostEclosionWindow : LifeStageWindow
  multigenerationWindow : LifeStageWindow
  sourceDefinedWindow : LifeStageWindow

data TissueRegion : Set where
  nervousSystemRegion : TissueRegion
  mushroomBodyOrClockNeuronRegion : TissueRegion
  ovaryRegion : TissueRegion
  testisRegion : TissueRegion
  larvalMidgutRegion : TissueRegion
  wholeOrganismReadout : TissueRegion

data MeasurementKind : Set where
  olfactoryMemoryAssay : MeasurementKind
  circadianSleepAssay : MeasurementKind
  ovaryGermlineAssay : MeasurementKind
  reproductiveCapacityAssay : MeasurementKind
  cometDNAAssay : MeasurementKind
  locomotorSurvivalAssay : MeasurementKind

data ExperimentalRole : Set where
  sourceObservationRole : ExperimentalRole
  trainingCarrierRole : ExperimentalRole
  heldOutCarrierRole : ExperimentalRole
  nullReplicateRole : ExperimentalRole

data ConnectomeRole : Set where
  noConnectomeProjection : ConnectomeRole
  structuralFibreProjection : FlyNDim.StructuralFibre → ConnectomeRole

record FlyPesticideSituatedObservation : Set where
  constructor fly-pesticide-situated-observation
  field
    study : Atlas.FlyPesticideStudy
    pesticide : PesticideIdentity
    organismIdentity : String
    experimentalLineOrGenotype : String
    lifeStageWindow : LifeStageWindow
    exposureDefinition : String
    tissueOrRegion : TissueRegion
    observationFamily : ObservationFamily
    measurementKind : MeasurementKind
    measurementDefinition : String
    experimentalRole : ExperimentalRole
    connectomeRole : ConnectomeRole
    sourceLocator : String
    paymentReading : String
open FlyPesticideSituatedObservation public

------------------------------------------------------------------------
-- Concrete source-bounded observation packets.  These records do not upgrade
-- the source claims; they only retain coordinates that the atlas already says
-- are required to interpret each study.
------------------------------------------------------------------------

thiaclopridSleepObservation : FlyPesticideSituatedObservation
thiaclopridSleepObservation = fly-pesticide-situated-observation
  Atlas.tasman2021
  thiaclopridIdentity
  "Drosophila melanogaster / Q130888 / NCBI taxon 7227"
  "source-defined fly line"
  adultWindow
  "field-relevant thiacloprid exposure as defined by Tasman et al. 2021"
  mushroomBodyOrClockNeuronRegion
  neuralBehaviourObservation
  circadianSleepAssay
  "sleep/circadian behavioural readout; thiacloprid is one of four separately retained neonicotinoids"
  sourceObservationRole
  noConnectomeProjection
  "Tasman et al. 2021 DOI 10.1038/s41598-021-81548-2 / PMID 33479461 / PMCID PMC7820356"
  "source-bounded neural/sleep observation only"

thiaclopridOvaryObservation : FlyPesticideSituatedObservation
thiaclopridOvaryObservation = fly-pesticide-situated-observation
  Atlas.sun2026Thiacloprid
  thiaclopridIdentity
  "Drosophila melanogaster / Q130888 / NCBI taxon 7227"
  "source-defined laboratory genotype"
  sourceDefinedWindow
  "0.5, 5 and 10 mg/L sublethal thiacloprid conditions as defined by Sun et al."
  ovaryRegion
  reproductiveObservation
  ovaryGermlineAssay
  "ovary residue/morphology, GSC/CB homeostasis, dpp/bam and escort-cell apoptosis readouts"
  sourceObservationRole
  noConnectomeProjection
  "Sun et al. 2026 DOI 10.1016/j.pestbp.2025.106811 / PMID 41350065"
  "source-bounded developmental/reproductive observation only"

dichlorvosRepairObservation : FlyPesticideSituatedObservation
dichlorvosRepairObservation = fly-pesticide-situated-observation
  Atlas.mishra2014Dichlorvos
  dichlorvosIdentity
  "Drosophila melanogaster / Q130888 / NCBI taxon 7227"
  "Oregon R+ and declared pre-/post-replication DNA-repair or oxidative-stress mutant"
  larvalWindow
  "48 h dichlorvos exposure at source-defined concentrations up to 15 ng/ml"
  larvalMidgutRegion
  genotoxicObservation
  cometDNAAssay
  "midgut-cell comet DNA-migration assay stratified by repair/oxidative-stress genotype"
  sourceObservationRole
  noConnectomeProjection
  "Mishra et al. 2014 DOI 10.1016/j.mrgentox.2014.02.004 / PMID 24614193"
  "source-bounded in-vivo genotoxicity observation only"

mixtureLifeHistoryObservation : FlyPesticideSituatedObservation
mixtureLifeHistoryObservation = fly-pesticide-situated-observation
  Atlas.kishore2026Mixture
  pesticideMixtureIdentity
  "Drosophila melanogaster / Q130888 / NCBI taxon 7227"
  "source-defined fly population"
  multigenerationWindow
  "source-defined pesticide mixture/formulations across LOQ/MRL-related concentration regimes"
  wholeOrganismReadout
  lifeHistoryObservation
  locomotorSurvivalAssay
  "survival and locomotion, with reproductive capacity retained as a distinct parallel endpoint"
  sourceObservationRole
  noConnectomeProjection
  "Kishore et al. 2026 DOI 10.1016/j.jenvman.2025.128324 / PMID 41418506"
  "source-bounded mixture/life-history observation only"

------------------------------------------------------------------------
-- Finite projection witnesses.
------------------------------------------------------------------------

data FlyObservationWorld : Set where
  thiaclopridSleepWorld : FlyObservationWorld
  thiaclopridOvaryWorld : FlyObservationWorld
  imidaclopridShortMemoryWorld : FlyObservationWorld
  imidaclopridLongMemoryWorld : FlyObservationWorld
  dichlorvosRepairWorld : FlyObservationWorld

data CoarseSpeciesIdentity : Set where
  drosophilaMelanogasterIdentity : CoarseSpeciesIdentity

data CoarseEndpointLabel : Set where
  memoryEndpoint : CoarseEndpointLabel
  pesticideResponseEndpoint : CoarseEndpointLabel

data MeasurementTimescale : Set where
  shortMemoryTimescale : MeasurementTimescale
  longMemoryTimescale : MeasurementTimescale
  nonMemoryTimescale : MeasurementTimescale

worldPesticide : FlyObservationWorld → PesticideIdentity
worldPesticide thiaclopridSleepWorld = thiaclopridIdentity
worldPesticide thiaclopridOvaryWorld = thiaclopridIdentity
worldPesticide imidaclopridShortMemoryWorld = imidaclopridIdentity
worldPesticide imidaclopridLongMemoryWorld = imidaclopridIdentity
worldPesticide dichlorvosRepairWorld = dichlorvosIdentity

worldSpecies : FlyObservationWorld → CoarseSpeciesIdentity
worldSpecies _ = drosophilaMelanogasterIdentity

worldObservationFamily : FlyObservationWorld → ObservationFamily
worldObservationFamily thiaclopridSleepWorld = neuralBehaviourObservation
worldObservationFamily thiaclopridOvaryWorld = reproductiveObservation
worldObservationFamily imidaclopridShortMemoryWorld = neuralBehaviourObservation
worldObservationFamily imidaclopridLongMemoryWorld = neuralBehaviourObservation
worldObservationFamily dichlorvosRepairWorld = genotoxicObservation

worldEndpointLabel : FlyObservationWorld → CoarseEndpointLabel
worldEndpointLabel imidaclopridShortMemoryWorld = memoryEndpoint
worldEndpointLabel imidaclopridLongMemoryWorld = memoryEndpoint
worldEndpointLabel _ = pesticideResponseEndpoint

worldMeasurementTimescale : FlyObservationWorld → MeasurementTimescale
worldMeasurementTimescale imidaclopridShortMemoryWorld = shortMemoryTimescale
worldMeasurementTimescale imidaclopridLongMemoryWorld = longMemoryTimescale
worldMeasurementTimescale _ = nonMemoryTimescale

pesticideIdentityCannotRecoverObservationFamily :
  INF.FactorsThrough worldPesticide worldObservationFamily → ⊥
pesticideIdentityCannotRecoverObservationFamily =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      thiaclopridSleepWorld
      thiaclopridOvaryWorld
      refl
      (λ ()))

speciesIdentityCannotRecoverObservationFamily :
  INF.FactorsThrough worldSpecies worldObservationFamily → ⊥
speciesIdentityCannotRecoverObservationFamily =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      thiaclopridSleepWorld
      dichlorvosRepairWorld
      refl
      (λ ()))

sameMemoryLabelCannotRecoverMeasurementTimescale :
  INF.FactorsThrough worldEndpointLabel worldMeasurementTimescale → ⊥
sameMemoryLabelCannotRecoverMeasurementTimescale =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      imidaclopridShortMemoryWorld
      imidaclopridLongMemoryWorld
      refl
      (λ ()))

------------------------------------------------------------------------
-- Repaired observation surface.
------------------------------------------------------------------------

record FlyToxicologyObservationSignature : Set where
  constructor fly-toxicology-observation-signature
  field
    pesticideIdentity : PesticideIdentity
    speciesIdentity : CoarseSpeciesIdentity
    family : ObservationFamily
    lifeStage : LifeStageWindow
    tissue : TissueRegion
    measurement : MeasurementKind
    measurementDefinition : String
    exposureDefinition : String
    sourceIdentity : String
    sourceLocator : String
open FlyToxicologyObservationSignature public

situatedSignature : FlyPesticideSituatedObservation → FlyToxicologyObservationSignature
situatedSignature observation = fly-toxicology-observation-signature
  (pesticide observation)
  drosophilaMelanogasterIdentity
  (observationFamily observation)
  (lifeStageWindow observation)
  (tissueOrRegion observation)
  (measurementKind observation)
  (measurementDefinition observation)
  (exposureDefinition observation)
  (Atlas.label (study observation))
  (sourceLocator observation)

------------------------------------------------------------------------
-- Existing experiment-design and Fly NDim owners remain authoritative for
-- experiment escalation and structural-fibre semantics.
------------------------------------------------------------------------

experimentDesignBoundary : Experiment.PesticideExperimentDesignBoundary
experimentDesignBoundary = Experiment.canonicalPesticideExperimentDesignBoundary

flyNDimBoundary : FlyNDim.FlyNDimStructureFunctionBoundary
flyNDimBoundary = FlyNDim.canonicalFlyNDimStructureFunctionBoundary

------------------------------------------------------------------------
-- WrongType / cross-pollination firewalls.
------------------------------------------------------------------------

data ConnectomeFibreCreatesToxicologyMechanism : Set where
data ToxicologyEndpointCreatesConnectomeMechanism : Set where
data PublicationIdentifierCreatesObservedEffect : Set where
data SameSpeciesCreatesSameExperimentalObject : Set where
data SameChemicalCreatesSameObservationDefinition : Set where

connectomeFibreDoesNotCreateToxicologyMechanism :
  ConnectomeFibreCreatesToxicologyMechanism → ⊥
connectomeFibreDoesNotCreateToxicologyMechanism ()

toxicologyEndpointDoesNotCreateConnectomeMechanism :
  ToxicologyEndpointCreatesConnectomeMechanism → ⊥
toxicologyEndpointDoesNotCreateConnectomeMechanism ()

publicationIdentifierDoesNotCreateObservedEffect :
  PublicationIdentifierCreatesObservedEffect → ⊥
publicationIdentifierDoesNotCreateObservedEffect ()

sameSpeciesDoesNotCreateSameExperimentalObject :
  SameSpeciesCreatesSameExperimentalObject → ⊥
sameSpeciesDoesNotCreateSameExperimentalObject ()

sameChemicalDoesNotCreateSameObservationDefinition :
  SameChemicalCreatesSameObservationDefinition → ⊥
sameChemicalDoesNotCreateSameObservationDefinition ()

record FlyPesticideSituatedObservationBoundary : Set where
  constructor fly-pesticide-situated-observation-boundary
  field
    pesticideIdentityInsufficientForObservation : Bool
    speciesIdentityInsufficientForObservation : Bool
    measurementDefinitionRetained : Bool
    exposureWindowRetained : Bool
    genotypeOrLineRetained : Bool
    tissueOrRegionRetained : Bool
    sourceProvenanceRetained : Bool
    sourceLocatorRetained : Bool
    flyNDimFibreSemanticsReused : Bool
    pesticideExperimentDesignReused : Bool
    connectomeFibreCreatesToxicologyMechanism : Bool
    toxicologyEndpointCreatesConnectomeMechanism : Bool
    identifiersCreateObservedEffect : Bool
    sameChemicalCreatesSameMeasurementObject : Bool
open FlyPesticideSituatedObservationBoundary public

canonicalFlyPesticideSituatedObservationBoundary : FlyPesticideSituatedObservationBoundary
canonicalFlyPesticideSituatedObservationBoundary =
  fly-pesticide-situated-observation-boundary
    true true true true true true true true true true
    false false false false
