module DASHI.Biology.AtomicMolecularBiologicalIncorporationHyperfabricExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Chemistry.AtomicMolecularReactionLineageHyperfabricExact as Lineage
import DASHI.Chemistry.ElectronBondTransportExact as Electron
import DASHI.Physics.Chemistry.AtomicPeriodicTable369ProteinDNA3DAdapterExact as ProteinDNA
import DASHI.Biology.Cell.CellStateAttractor as Cell
import DASHI.Biology.Levin.ProblemSpaceAgency as Levin

------------------------------------------------------------------------
-- MOLECULAR LINEAGE -> BIOLOGICAL CARRIER HYPERFABRIC
--
-- Biological incorporation is not material identity collapse.  The same atoms
-- and electrons can participate in different proteins, nucleic acids,
-- membranes, metabolites and cellular histories.  This bridge preserves the
-- upstream material lineage while requiring new biological organisation,
-- geometry, regulatory and functional witnesses.
------------------------------------------------------------------------

data BiologicalCarrierKind : Set where
  proteinCarrier : BiologicalCarrierKind
  dnaCarrier : BiologicalCarrierKind
  rnaCarrier : BiologicalCarrierKind
  membraneCarrier : BiologicalCarrierKind
  metaboliteCarrier : BiologicalCarrierKind
  cofactorCarrier : BiologicalCarrierKind
  organelleCarrier : BiologicalCarrierKind
  extracellularCarrier : BiologicalCarrierKind

record BiologicalIncorporationReceipt : Set₁ where
  constructor biologicalIncorporationReceipt
  field
    sourceMolecules : List Lineage.MolecularLineageState
    sourceReactionReference : String
    targetCarrierKind : BiologicalCarrierKind
    targetCarrierReference : String
    atomLineageMappingReference : String
    electronLineageMappingReference : String
    bondAndGeometryInheritanceReference : String
    newBondFormationReference : String
    proteinOrNucleicAcidSequenceReference : String
    foldingOrHelicalGeometryReference : String
    compartmentReference : String
    regulatoryContextReference : String
    cellStateCoordinateReference : String
    developmentalHistoryReference : String
    functionalObservationReference : String
    problemSpaceReference : String
    residualReference : String
    provenanceReference : String

open BiologicalIncorporationReceipt public

record BiologicalLineageObserver : Set where
  constructor biologicalLineageObserver
  field
    carrierReference : String
    observerReference : String
    observedCoordinateReference : String
    hiddenMaterialLineageReference : String
    hiddenElectronicStateReference : String
    hiddenGeometryReference : String
    consumerReference : String
    refinementReference : String

open BiologicalLineageObserver public

------------------------------------------------------------------------
-- Existing surfaces are explicit donors.
------------------------------------------------------------------------

proteinDNA3DBoundary : ProteinDNA.ProteinDNA3DAdapterBoundary
proteinDNA3DBoundary = ProteinDNA.canonicalProteinDNA3DAdapterBoundary

cellStateSurface : Set₁
cellStateSurface = Cell.CoupledCellState

stressToCellStateSurface :
  Cell.CoupledCellState → Set₁
stressToCellStateSurface = Cell.StressResponseCellStateBridge

problemSpaceBoundary : Levin.ProblemSpaceAgencyBoundary
problemSpaceBoundary = Levin.canonicalProblemSpaceAgencyBoundary

------------------------------------------------------------------------
-- Promotion / non-collapse boundary.
------------------------------------------------------------------------

record AtomicMolecularBiologicalIncorporationBoundary : Set where
  constructor atomicMolecularBiologicalIncorporationBoundary
  field
    upstreamMaterialLineageRetained : Bool
    upstreamMaterialLineageRetainedIsTrue :
      upstreamMaterialLineageRetained ≡ true

    upstreamElectronLineageRetainedWhenKnown : Bool
    upstreamElectronLineageRetainedWhenKnownIsTrue :
      upstreamElectronLineageRetainedWhenKnown ≡ true

    sameAtomInventoryImpliesSameBiologicalCarrier : Bool
    sameAtomInventoryImpliesSameBiologicalCarrierIsFalse :
      sameAtomInventoryImpliesSameBiologicalCarrier ≡ false

    sameMolecularSpeciesImpliesSameProteinOrDNAContext : Bool
    sameMolecularSpeciesImpliesSameProteinOrDNAContextIsFalse :
      sameMolecularSpeciesImpliesSameProteinOrDNAContext ≡ false

    sequenceDefinitionallyDeterminesUniqueThreeDState : Bool
    sequenceDefinitionallyDeterminesUniqueThreeDStateIsFalse :
      sequenceDefinitionallyDeterminesUniqueThreeDState ≡ false

    oneProteinModificationEqualsWholeCellState : Bool
    oneProteinModificationEqualsWholeCellStateIsFalse :
      oneProteinModificationEqualsWholeCellState ≡ false

    biologicalFunctionDeterminedByElectronLineageAlone : Bool
    biologicalFunctionDeterminedByElectronLineageAloneIsFalse :
      biologicalFunctionDeterminedByElectronLineageAlone ≡ false

    biologicalObserverMayCollapseMaterialDistinctions : Bool
    biologicalObserverMayCollapseMaterialDistinctionsIsTrue :
      biologicalObserverMayCollapseMaterialDistinctions ≡ true

    collapsedMaterialDistinctionMayNeedRefinement : Bool
    collapsedMaterialDistinctionMayNeedRefinementIsTrue :
      collapsedMaterialDistinctionMayNeedRefinement ≡ true

    problemSpaceAgencyPromotedFromChemistryAlone : Bool
    problemSpaceAgencyPromotedFromChemistryAloneIsFalse :
      problemSpaceAgencyPromotedFromChemistryAlone ≡ false

open AtomicMolecularBiologicalIncorporationBoundary public

canonicalAtomicMolecularBiologicalIncorporationBoundary :
  AtomicMolecularBiologicalIncorporationBoundary
canonicalAtomicMolecularBiologicalIncorporationBoundary =
  atomicMolecularBiologicalIncorporationBoundary
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
    true refl
    false refl
