module DASHI.Biology.BiologicalRecoveryBoundary where

open import DASHI.Physics.Chemistry.AtomicPeriodicTableRecoveryBoundary
open import DASHI.Biology.Molecular.MolecularAssemblyBoundary
open import DASHI.Biology.Origins.AutocatalyticCompartmentBoundary
open import DASHI.Biology.Genetics.ConstraintPersistence
open import DASHI.Biology.Genetics.BiologicalConstraintLanguage
open import DASHI.Biology.Protein.ProteinRecoveryBoundary
open import DASHI.Biology.Cell.CellRecoveryBoundary
open import DASHI.Biology.Morphogenesis.MorphogenesisRecoveryBoundary
open import DASHI.Biology.Agency.ScaleIndexedAgency
open import DASHI.Biology.Organism.OrganismHomeostasis
open import DASHI.Biology.Evolution.EvolutionaryPopulationDynamics
open import DASHI.Biology.Ecology.EcologicalInteractionDynamics

-- Full recovery tower.  Every scale transition is a separately witnessed bridge;
-- the record does not promote atomic chemistry directly into life or agency.
record BiologicalRecoveryBoundary : Set₁ where
  field
    atomicChemistry : AtomicPeriodicTableRecoveryBoundary
    molecularChemistry : MolecularAssemblySystem
    prebioticChemistry : PrebioticChemicalSystem
    hereditySystem : HereditaryRewriteSystem
    biologicalLanguage : BiologicalPushdownSystem
    proteinSystem : ProteinRecoveryBoundary
    cellSystem : CellRecoveryBoundary
    morphogenesisSystem : MorphogenesisRecoveryBoundary
    agencySystem : ScaleIndexedAgencySystem
    organismSystem : OrganismControlSystem
    evolutionSystem : EvolutionarySystem
    ecologicalSystem : EcologicalSystem

    AtomicToMolecular : Set
    ChemistryToDissipativeCycles : Set
    CyclesToHereditaryConstraints : Set
    ConstraintLanguageToProteinSequence : Set
    MoleculeSequenceToProteinDynamics : Set
    ProteinNetworksToCells : Set
    CellsToTissuesAndMorphogenesis : Set
    TissuesToOrganismIntegration : Set
    OrganismsToPopulationEvolution : Set
    PopulationsToEcologicalDynamics : Set

    atomicMolecularWitness : AtomicToMolecular
    dissipativeCycleWitness : ChemistryToDissipativeCycles
    hereditaryConstraintWitness : CyclesToHereditaryConstraints
    languageProteinWitness : ConstraintLanguageToProteinSequence
    proteinDynamicsWitness : MoleculeSequenceToProteinDynamics
    proteinCellWitness : ProteinNetworksToCells
    cellMorphogenesisWitness : CellsToTissuesAndMorphogenesis
    tissueOrganismWitness : TissuesToOrganismIntegration
    organismEvolutionWitness : OrganismsToPopulationEvolution
    populationEcologyWitness : PopulationsToEcologicalDynamics

    -- Integration points for the focused existing lanes: agentic materials,
    -- predictive agency, prion templating, and the typed Levin programme.
    AgenticMaterialsControlIntegrated : Set
    PredictiveAgencyIntegrated : Set
    FocusedPrionLaneIntegrated : Set
    LevinBioelectricCoreIntegrated : Set

    agenticMaterialsWitness : AgenticMaterialsControlIntegrated
    predictiveAgencyWitness : PredictiveAgencyIntegrated
    focusedPrionWitness : FocusedPrionLaneIntegrated
    levinCoreWitness : LevinBioelectricCoreIntegrated

record BiologicalRecoveryWitness
  (B : BiologicalRecoveryBoundary) : Set₁ where
  field
    MolecularAssemblyRecovered : Set
    ProteinSequenceAndConformationRecovered : Set
    ContextualProteinFunctionRecovered : Set
    OpenCellularViabilityRecovered : Set
    MorphogeneticControlRecovered : Set
    OrganismIntegrationRecovered : Set
    EvolutionaryDynamicsRecovered : Set
    EcologicalDynamicsRecovered : Set

    molecularWitness : MolecularAssemblyRecovered
    proteinWitness : ProteinSequenceAndConformationRecovered
    functionWitness : ContextualProteinFunctionRecovered
    cellWitness : OpenCellularViabilityRecovered
    morphogenesisWitness : MorphogeneticControlRecovered
    organismWitness : OrganismIntegrationRecovered
    evolutionWitness : EvolutionaryDynamicsRecovered
    ecologyWitness : EcologicalDynamicsRecovered

record BiologicalOpenObligations
  (B : BiologicalRecoveryBoundary) : Set₁ where
  field
    atomicManyBodyChemistry : Set
    molecularReactionAndStereochemistry : Set
    originOfLifeCycleExistenceAndRobustness : Set
    hereditaryConstraintRealisation : Set
    translationAndFoldingDynamics : Set
    proteinFunctionExperimentalValidation : Set
    membraneMetabolismViabilityClosure : Set
    regulatoryBioelectricMechanicalCoupling : Set
    localToGlobalMorphogeneticControllability : Set
    regenerativeRepairAcrossContexts : Set
    developmentalGenomicInverseCalibration : Set
    organismIntegrationAndBehaviour : Set
    evolutionEcologyDataAuthority : Set

-- Promotion statuses keep operational biological content separate from stronger
-- philosophical, clinical, or universal claims.
data BiologicalPromotionStatus : Set where
  candidateRecoveryTower : BiologicalPromotionStatus
  empiricalCalibrationRequired : BiologicalPromotionStatus
  consciousnessNotDerived : BiologicalPromotionStatus
  panpsychismNotDerived : BiologicalPromotionStatus
  retrocausalityNotDerived : BiologicalPromotionStatus
  clinicalAuthorityNotDerived : BiologicalPromotionStatus

biologicalRecoveryAvailable :
  {B : BiologicalRecoveryBoundary} →
  BiologicalRecoveryWitness B → BiologicalRecoveryWitness B
biologicalRecoveryAvailable witness = witness
