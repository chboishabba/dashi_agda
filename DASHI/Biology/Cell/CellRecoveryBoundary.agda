module DASHI.Biology.Cell.CellRecoveryBoundary where

import DASHI.Biology.Cell.SelectiveMembraneBoundary as Membrane
import DASHI.Biology.Cell.OpenMetabolicNetwork as Metabolism
import DASHI.Biology.Cell.CellViabilityKernel as Viability
import DASHI.Biology.Cell.CellStateAttractor as CellState
import DASHI.Biology.Cell.BioelectricNetwork as Bioelectric

record CellRecoveryBoundary : Set₁ where
  field
    membraneSystem   : Membrane.SelectiveMembraneSystem
    metabolicNetwork : Metabolism.OpenMetabolicNetwork
    viabilitySystem  : Viability.CellViabilitySystem
    cellState        : CellState.CoupledCellState
    bioelectric      : Bioelectric.BioelectricNetwork

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
