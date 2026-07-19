module DASHI.Biology.Cell.CellRecoveryBoundary where

open import DASHI.Biology.Cell.SelectiveMembraneBoundary
open import DASHI.Biology.Cell.OpenMetabolicNetwork
open import DASHI.Biology.Cell.CellViabilityKernel
open import DASHI.Biology.Cell.CellStateAttractor
open import DASHI.Biology.Cell.BioelectricNetwork

record CellRecoveryBoundary : Set₁ where
  field
    membraneSystem   : SelectiveMembraneSystem
    metabolicNetwork : OpenMetabolicNetwork
    viabilitySystem  : CellViabilitySystem
    cellState        : CoupledCellState
    bioelectric      : BioelectricNetwork

    ProteinToReactionNetwork : Set
    ReactionNetworkToOpenMetabolism : Set
    MembraneMetabolismCoupling : Set
    RegulationToCellState : Set
    BioelectricChemicalMechanicalCoupling : Set
    CellStateToViability : Set

    proteinReactionWitness : ProteinToReactionNetwork
    openMetabolismWitness  : ReactionNetworkToOpenMetabolism
    membraneMetabolismWitness : MembraneMetabolismCoupling
    regulationCellStateWitness : RegulationToCellState
    coupledControlWitness : BioelectricChemicalMechanicalCoupling
    viabilityWitness : CellStateToViability

record CellRecoveryWitness
  (C : CellRecoveryBoundary) : Set₁ where
  field
    CompartmentRecovered : Set
    MetabolismRecovered  : Set
    ViabilityRecovered   : Set
    CellStateAttractorsRecovered : Set
    BioelectricControlRecovered : Set

    compartmentWitness : CompartmentRecovered
    metabolismWitness  : MetabolismRecovered
    viabilityWitness   : ViabilityRecovered
    cellStateWitness   : CellStateAttractorsRecovered
    bioelectricWitness : BioelectricControlRecovered

record CellOpenObligations
  (C : CellRecoveryBoundary) : Set₁ where
  field
    selectiveTransportCalibration : Set
    nontrivialDissipativeCycleExistence : Set
    boundedOpenSystemDynamics : Set
    regulatoryAttractorValidation : Set
    bioelectricPatternIntervention : Set
    organelleAndCytoskeletalCoupling : Set

cellRecoveryAvailable :
  {C : CellRecoveryBoundary} →
  CellRecoveryWitness C → CellRecoveryWitness C
cellRecoveryAvailable witness = witness
