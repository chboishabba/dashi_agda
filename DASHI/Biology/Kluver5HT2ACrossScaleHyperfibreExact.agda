module DASHI.Biology.Kluver5HT2ACrossScaleHyperfibreExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Biology.KluverLogPolar5HT2ASourceAtlasExact as Sources
import DASHI.Biology.NeurochemicalAtomicChemistryBridge as AtomicChem
import DASHI.Biology.NeurochemicalProteinTargetBridge as ProteinTarget
import DASHI.Biology.NeurochemicalTransmissionBridge as Transmission
import DASHI.Biology.NeurochemicalBrainCarrierBridge as Brain
import DASHI.Biology.Protein.ProteinConformationAttractor as ProteinConformation
import DASHI.Physics.Chemistry.AtomicPeriodicTable369ChemistryHyperfibreBridgeExact as Chemistry369
import DASHI.Cognition.Kluver5HT2ACrossPollinationExact as Kluver5HT2A

------------------------------------------------------------------------
-- CROSS-SCALE HYPERFIBRE
--
-- Existing repo owners already separate:
--
--   atom / valence / molecular identity
--     -> neurochemical molecular chemistry
--     -> protein target / receptor context
--     -> receptor occupancy / neurochemical transmission
--     -> brain/circuit carrier
--     -> cortical geometry / Kluever phenomenology.
--
-- This module composes those owners without turning any arrow into an
-- identity.  The empirical 5-HT2A source rows remain those in
-- KluverLogPolar5HT2ASourceAtlasExact.  The cross-scale composition below is a
-- DASHI extension and must not be attributed back to those source authors.
------------------------------------------------------------------------

sourceAtlas : Source.AttributedSourceAtlas
sourceAtlas = Sources.canonicalKluverLogPolar5HT2AAtlas

------------------------------------------------------------------------
-- Canonical existing-owner witnesses.
------------------------------------------------------------------------

atomicChemistryBridge : AtomicChem.NeurochemicalAtomicChemistryBridge
atomicChemistryBridge = AtomicChem.canonicalNeurochemicalAtomicChemistryBridge

proteinTargetBridge : ProteinTarget.NeurochemicalProteinTargetBridge
proteinTargetBridge = ProteinTarget.canonicalNeurochemicalProteinTargetBridge

transmissionBridge : Transmission.NeurochemicalTransmissionBridge
transmissionBridge = Transmission.canonicalNeurochemicalTransmissionBridge

brainCarrierBridge : Brain.NeurochemicalBrainCarrierBridge
brainCarrierBridge = Brain.canonicalNeurochemicalBrainCarrierBridge

atomicChemistryBoundary : Chemistry369.AtomicChemistryCrossPollinationBoundary
atomicChemistryBoundary = Chemistry369.canonicalAtomicChemistryCrossPollinationBoundary

kluver5HT2ABridge : Kluver5HT2A.Kluver5HT2ACrossPollination
kluver5HT2ABridge = Kluver5HT2A.canonicalKluver5HT2ACrossPollination

------------------------------------------------------------------------
-- Scale coordinates.
------------------------------------------------------------------------

data FiveHT2AScale : Set where
  atomicElectronicScale : FiveHT2AScale
  molecularLigandScale : FiveHT2AScale
  proteinReceptorScale : FiveHT2AScale
  bindingOccupancyScale : FiveHT2AScale
  transmissionScale : FiveHT2AScale
  cellCircuitScale : FiveHT2AScale
  corticalModeScale : FiveHT2AScale
  perceptualProjectionScale : FiveHT2AScale

data CrossScaleLinkStatus : Set where
  existingRepoBridge : CrossScaleLinkStatus
  sourceBoundEmpiricalCoordinate : CrossScaleLinkStatus
  dashiCompositeCandidate : CrossScaleLinkStatus
  notRecovered : CrossScaleLinkStatus

record FiveHT2ACrossScaleLink : Set where
  constructor fiveHT2ACrossScaleLink
  field
    sourceScale : FiveHT2AScale
    targetScale : FiveHT2AScale
    status : CrossScaleLinkStatus
    owner : String
    boundary : String

open FiveHT2ACrossScaleLink public

atomicToMolecularLink : FiveHT2ACrossScaleLink
atomicToMolecularLink =
  fiveHT2ACrossScaleLink
    atomicElectronicScale
    molecularLigandScale
    existingRepoBridge
    "DASHI.Physics.Chemistry.AtomicPeriodicTable369ChemistryHyperfibreBridgeExact / DASHI.Biology.NeurochemicalAtomicChemistryBridge"
    "atomic/valence information constrains molecular candidates but does not uniquely determine molecular identity, geometry, protonation, conformation, binding, kinetics, or biological action"

molecularToProteinTargetLink : FiveHT2ACrossScaleLink
molecularToProteinTargetLink =
  fiveHT2ACrossScaleLink
    molecularLigandScale
    proteinReceptorScale
    existingRepoBridge
    "DASHI.Biology.BioactiveMolecularRecognitionBridge / DASHI.Biology.NeurochemicalProteinTargetBridge"
    "ligand/receptor recognition is candidate-only; molecular shape or identity does not by itself prove receptor-action identity, efficacy, pathway, or folding state"

proteinToOccupancyLink : FiveHT2ACrossScaleLink
proteinToOccupancyLink =
  fiveHT2ACrossScaleLink
    proteinReceptorScale
    bindingOccupancyScale
    dashiCompositeCandidate
    "DASHI.Biology.NeurochemicalProteinTargetBridge -> DASHI.Biology.NeurochemicalTransmissionBridge"
    "protein target context and binding-site/conformation candidates may feed occupancy candidates, but quantitative affinity, concentration, kinetics, receptor state, and assay receipts remain separate obligations"

occupancyToTransmissionLink : FiveHT2ACrossScaleLink
occupancyToTransmissionLink =
  fiveHT2ACrossScaleLink
    bindingOccupancyScale
    transmissionScale
    existingRepoBridge
    "DASHI.Biology.NeurochemicalTransmissionBridge"
    "receptor occupancy is one carrier among synaptic, extrasynaptic, transporter, enzyme, concentration-timecourse, neural-encoding and plasticity coordinates; occupancy does not equal neural effect"

transmissionToBrainLink : FiveHT2ACrossScaleLink
transmissionToBrainLink =
  fiveHT2ACrossScaleLink
    transmissionScale
    cellCircuitScale
    existingRepoBridge
    "DASHI.Biology.NeurochemicalBrainCarrierBridge"
    "neurochemical transmission enters a candidate brain/circuit context with cell type, region, encoding and plasticity residuals; brain-state recovery and behavior causation remain blocked"

brainToCorticalModeLink : FiveHT2ACrossScaleLink
brainToCorticalModeLink =
  fiveHT2ACrossScaleLink
    cellCircuitScale
    corticalModeScale
    dashiCompositeCandidate
    "DASHI.Biology.NeurochemicalBrainCarrierBridge x DASHI.Cognition.Kluver5HT2ACrossPollinationExact"
    "5-HT2A-dependent network/relevance changes may modulate conditions under which endogenous visual modes are selected, but the repo has no quantitative receptor-to-V1 mode-selection transfer law"

corticalModeToPerceptLink : FiveHT2ACrossScaleLink
corticalModeToPerceptLink =
  fiveHT2ACrossScaleLink
    corticalModeScale
    perceptualProjectionScale
    existingRepoBridge
    "DASHI.Cognition.LogPolarKluverDerivationExact / DASHI.Cognition.CorticalLogPolarProjectionGeometry"
    "selected cortical geometry can be projected through the finite log-polar/Kluever relation; projection is lossy, partial, and non-invertible"

canonicalFiveHT2ACrossScaleLinks : List FiveHT2ACrossScaleLink
canonicalFiveHT2ACrossScaleLinks =
  atomicToMolecularLink
  ∷ molecularToProteinTargetLink
  ∷ proteinToOccupancyLink
  ∷ occupancyToTransmissionLink
  ∷ transmissionToBrainLink
  ∷ brainToCorticalModeLink
  ∷ corticalModeToPerceptLink
  ∷ []

------------------------------------------------------------------------
-- Protein-conformation reuse.
--
-- Actual owner type, retained without constructing an HTR2A-specific instance.
proteinConformationSystemType : Set₁
proteinConformationSystemType =
  ProteinConformation.ProteinConformationSystem

--
-- 5-HT2A is treated at this level only as a protein/receptor target context.
-- The existing ProteinConformationSystem is retained because receptor state is
-- not definitionally a single static structure.  No concrete HTR2A folding or
-- allosteric landscape is manufactured here.
------------------------------------------------------------------------

record ReceptorConformationInterface : Set where
  constructor receptorConformationInterface
  field
    proteinConformationOwner : String
    proteinConformationSystemAvailable : Bool
    proteinConformationSystemAvailableIsTrue :
      proteinConformationSystemAvailable ≡ true

    receptorStateDependsOnConformation : Bool
    receptorStateDependsOnConformationIsTrue :
      receptorStateDependsOnConformation ≡ true

    singleStaticConformationAssumed : Bool
    singleStaticConformationAssumedIsFalse :
      singleStaticConformationAssumed ≡ false

    ligandIdentityAloneDeterminesConformation : Bool
    ligandIdentityAloneDeterminesConformationIsFalse :
      ligandIdentityAloneDeterminesConformation ≡ false

    foldingLandscapeRecoveredHere : Bool
    foldingLandscapeRecoveredHereIsFalse :
      foldingLandscapeRecoveredHere ≡ false

canonicalReceptorConformationInterface : ReceptorConformationInterface
canonicalReceptorConformationInterface =
  receptorConformationInterface
    "DASHI.Biology.Protein.ProteinConformationAttractor.ProteinConformationSystem"
    true refl
    true refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Exact anti-collapse propositions.
------------------------------------------------------------------------

data AtomicStateDeterminesPsychedelicPercept : Set where

data LigandIdentityDeterminesReceptorAction : Set where

data ReceptorOccupancyDeterminesBrainState : Set where

data BrainRegionActivationDeterminesKluverForm : Set where

data KluverFormDeterminesMolecularCause : Set where

atomicStateDoesNotDeterminePsychedelicPercept :
  AtomicStateDeterminesPsychedelicPercept → ⊥
atomicStateDoesNotDeterminePsychedelicPercept ()

ligandIdentityDoesNotDetermineReceptorAction :
  LigandIdentityDeterminesReceptorAction → ⊥
ligandIdentityDoesNotDetermineReceptorAction ()

receptorOccupancyDoesNotDetermineBrainState :
  ReceptorOccupancyDeterminesBrainState → ⊥
receptorOccupancyDoesNotDetermineBrainState ()

brainRegionActivationDoesNotDetermineKluverForm :
  BrainRegionActivationDeterminesKluverForm → ⊥
brainRegionActivationDoesNotDetermineKluverForm ()

kluverFormDoesNotDetermineMolecularCause :
  KluverFormDeterminesMolecularCause → ⊥
kluverFormDoesNotDetermineMolecularCause ()

------------------------------------------------------------------------
-- Cross-scale bundle.
------------------------------------------------------------------------

record Kluver5HT2ACrossScaleHyperfibre : Set₁ where
  constructor kluver5HT2ACrossScaleHyperfibre
  field
    chemistryBridge :
      AtomicChem.NeurochemicalAtomicChemistryBridge

    proteinBridge :
      ProteinTarget.NeurochemicalProteinTargetBridge

    neurochemicalBridge :
      Transmission.NeurochemicalTransmissionBridge

    brainBridge :
      Brain.NeurochemicalBrainCarrierBridge

    chemistryBoundary :
      Chemistry369.AtomicChemistryCrossPollinationBoundary

    receptorConformation :
      ReceptorConformationInterface

    visualBridge :
      Kluver5HT2A.Kluver5HT2ACrossPollination

    links :
      List FiveHT2ACrossScaleLink

    atomToPerceptIsNotIdentity : Bool
    atomToPerceptIsNotIdentityIsTrue :
      atomToPerceptIsNotIdentity ≡ true

    chemistryProteinBrainVisualLayersRemainDistinct : Bool
    chemistryProteinBrainVisualLayersRemainDistinctIsTrue :
      chemistryProteinBrainVisualLayersRemainDistinct ≡ true

    receptorToCorticalModeTransferIsQuantitativelyClosed : Bool
    receptorToCorticalModeTransferIsQuantitativelyClosedIsFalse :
      receptorToCorticalModeTransferIsQuantitativelyClosed ≡ false

    receptorConformationalLandscapeIsRecovered : Bool
    receptorConformationalLandscapeIsRecoveredIsFalse :
      receptorConformationalLandscapeIsRecovered ≡ false

    receptorOccupancyDoseResponseIsRecovered : Bool
    receptorOccupancyDoseResponseIsRecoveredIsFalse :
      receptorOccupancyDoseResponseIsRecovered ≡ false

    brainStateIsRecoveredFromChemistry : Bool
    brainStateIsRecoveredFromChemistryIsFalse :
      brainStateIsRecoveredFromChemistry ≡ false

    visualPhenomenologyIsRecoveredFromMolecularState : Bool
    visualPhenomenologyIsRecoveredFromMolecularStateIsFalse :
      visualPhenomenologyIsRecoveredFromMolecularState ≡ false

open Kluver5HT2ACrossScaleHyperfibre public

canonicalKluver5HT2ACrossScaleHyperfibre :
  Kluver5HT2ACrossScaleHyperfibre
canonicalKluver5HT2ACrossScaleHyperfibre =
  kluver5HT2ACrossScaleHyperfibre
    atomicChemistryBridge
    proteinTargetBridge
    transmissionBridge
    brainCarrierBridge
    atomicChemistryBoundary
    canonicalReceptorConformationInterface
    kluver5HT2ABridge
    canonicalFiveHT2ACrossScaleLinks
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Highest-alpha next obligations.
------------------------------------------------------------------------

record Kluver5HT2ACrossScaleFrontier : Set where
  constructor kluver5HT2ACrossScaleFrontier
  field
    firstMolecularGap : String
    firstProteinGap : String
    firstNeurochemicalGap : String
    firstBrainGap : String
    firstVisualGap : String
    preferredExperiment : String

canonicalKluver5HT2ACrossScaleFrontier :
  Kluver5HT2ACrossScaleFrontier
canonicalKluver5HT2ACrossScaleFrontier =
  kluver5HT2ACrossScaleFrontier
    "instantiate serotonin/LSD and 5-HT2A with assay-bound molecular identity, concentration, affinity/selectivity and kinetics rather than generic candidate units"
    "instantiate HTR2A receptor-state / binding-site / conformational-state evidence without equating ligand identity with agonist efficacy or signaling bias"
    "bind receptor occupancy to concentration-timecourse and downstream signaling observations under an explicit protocol"
    "derive a measured receptor/network perturbation -> visual-circuit state transfer with cell-type, region, temporal and observation-quotient receipts"
    "replace the finite qualitative mode relation with the analytic log-polar phase law and compare predicted form classes against frozen percept/fMRI observations"
    "paired perturbation design: receptor pharmacology + region/network readout + visual-form report, with each layer independently measured so cross-scale arrows can be tested rather than assumed"
