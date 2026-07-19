module DASHI.Biology.BiologicalRecoveryBoundary where

open import Agda.Primitive using (Setω)

import DASHI.Physics.Laws.PhysicalLawRecoveryBoundary as Physical
import DASHI.Physics.Chemistry.AtomicPeriodicTableRecoveryBoundary as Atomic
import DASHI.Biology.Molecular.MolecularAssemblyBoundary as Molecular
import DASHI.Biology.Origins.AutocatalyticCompartmentBoundary as Origins
import DASHI.Biology.Genetics.ConstraintPersistence as Heredity
import DASHI.Biology.Genetics.BiologicalConstraintLanguage as Language
import DASHI.Biology.Protein.ProteinRecoveryBoundary as Protein
import DASHI.Biology.Cell.CellRecoveryBoundary as Cell
import DASHI.Biology.Morphogenesis.MorphogenesisRecoveryBoundary as Morphogenesis
import DASHI.Biology.Agency.ScaleIndexedAgency as Agency
import DASHI.Biology.Organism.OrganismHomeostasis as Organism
import DASHI.Biology.Evolution.EvolutionaryPopulationDynamics as Evolution
import DASHI.Biology.Ecology.EcologicalInteractionDynamics as Ecology

-- Full recovery tower.  Every scale transition is a separately witnessed bridge;
-- the record does not promote physical law structure directly into life or
-- agency, nor atomic chemistry directly into cellular organisation.
record BiologicalRecoveryBoundary : Setω where
  field
    physicalLaws : Physical.PhysicalLawRecoveryBoundary
    atomicChemistry : Atomic.AtomicPeriodicTableRecoveryBoundary
    molecularChemistry : Molecular.MolecularAssemblySystem
    prebioticChemistry : Origins.PrebioticChemicalSystem
    hereditySystem : Heredity.HereditaryRewriteSystem
    biologicalLanguage : Language.BiologicalPushdownSystem
    proteinSystem : Protein.ProteinRecoveryBoundary
    cellSystem : Cell.CellRecoveryBoundary
    morphogenesisSystem : Morphogenesis.MorphogenesisRecoveryBoundary
    agencySystem : Agency.ScaleIndexedAgencySystem
    organismSystem : Organism.OrganismControlSystem
    evolutionSystem : Evolution.EvolutionarySystem
    ecologicalSystem : Ecology.EcologicalSystem

    PhysicalLawsToAtomicChemistry : Set
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

    physicalAtomicWitness : PhysicalLawsToAtomicChemistry
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
  (B : BiologicalRecoveryBoundary) : Setω where
  field
    PhysicalLawTowerRecovered : Set
    MolecularAssemblyRecovered : Set
    ProteinSequenceAndConformationRecovered : Set
    ContextualProteinFunctionRecovered : Set
    OpenCellularViabilityRecovered : Set
    MorphogeneticControlRecovered : Set
    OrganismIntegrationRecovered : Set
    EvolutionaryDynamicsRecovered : Set
    EcologicalDynamicsRecovered : Set

    physicalLawWitness : PhysicalLawTowerRecovered
    molecularWitness : MolecularAssemblyRecovered
    proteinWitness : ProteinSequenceAndConformationRecovered
    functionWitness : ContextualProteinFunctionRecovered
    cellWitness : OpenCellularViabilityRecovered
    morphogenesisWitness : MorphogeneticControlRecovered
    organismWitness : OrganismIntegrationRecovered
    evolutionWitness : EvolutionaryDynamicsRecovered
    ecologyWitness : EcologicalDynamicsRecovered

record BiologicalOpenObligations
  (B : BiologicalRecoveryBoundary) : Setω where
  field
    physicalLawTheoremLimitAndCalibrationClosure : Set
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
