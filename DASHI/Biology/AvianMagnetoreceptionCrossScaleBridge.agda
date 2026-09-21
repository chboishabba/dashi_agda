module DASHI.Biology.AvianMagnetoreceptionCrossScaleBridge where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Biology.AvianHepaticMacrophageMagnetoreception as Hepatic
import DASHI.Biology.CellDifferentiationCommunicationBridge as Cell
import DASHI.Biology.ProteinHormoneChemistryCellBridge as ProteinCell
import DASHI.Biology.EmbodiedMotorMultisensoryBridge as Embodied
import DASHI.Biology.NeurochemicalTransmissionBridge as Neuro
import DASHI.Biology.JasonThomasSTINGFerritinophagyMechanismDepthExact as Iron
import Ontology.Brain.BrainVocabularySurface as Brain

------------------------------------------------------------------------
-- Cross-scale magnetoreception bridge.
--
-- Existing owners are reused rather than duplicated:
--   ferritin/NCOA4/iron homeostasis
--   -> protein/cell chemistry boundary
--   -> cell/immune physiology
--   -> hepatic macrophage magnetic material
--   -> candidate peripheral afference
--   -> multisensory/interoceptive integration
--   -> brain-side observation vocabulary.
--
-- The arrows are typed as adjacency/compatibility seams, not as a derivation
-- of magnetoreception from atomic physics or of phenomenal content from brain
-- state.
------------------------------------------------------------------------

data MagnetoreceptionScale : Set where
  atomicIronScale : MagnetoreceptionScale
  proteinFerritinScale : MagnetoreceptionScale
  cellularMacrophageScale : MagnetoreceptionScale
  tissueHepaticScale : MagnetoreceptionScale
  peripheralAfferentScale : MagnetoreceptionScale
  multisensoryIntegrationScale : MagnetoreceptionScale
  brainObservationScale : MagnetoreceptionScale
  navigationPolicyScale : MagnetoreceptionScale
  phenomenalResidualScale : MagnetoreceptionScale

data CrossScaleRelation : Set where
  ironHomeostasisAdjacency : CrossScaleRelation
  proteinCellCompatibility : CrossScaleRelation
  immuneCellCompatibility : CrossScaleRelation
  magneticMaterialCompatibility : CrossScaleRelation
  peripheralCentralCandidateTransport : CrossScaleRelation
  multisensoryFusionCandidate : CrossScaleRelation
  brainObservationCompatibility : CrossScaleRelation
  policyConsumptionCompatibility : CrossScaleRelation

data CrossScaleBoundary : Set where
  noAtomicIronToSensorDerivation : CrossScaleBoundary
  noFerritinToSuperparamagnetismDerivation : CrossScaleBoundary
  noImmuneIdentityToMagnetoreceptorSufficiency : CrossScaleBoundary
  noAnatomicalProximityToNeuralCodePromotion : CrossScaleBoundary
  noPeripheralSignalToBrainStateRecovery : CrossScaleBoundary
  noBrainObservationToQualiaRecovery : CrossScaleBoundary
  noSensorFusionClosureClaim : CrossScaleBoundary
  noSingleCueNavigationClosureClaim : CrossScaleBoundary

canonicalMagnetoreceptionScales : List MagnetoreceptionScale
canonicalMagnetoreceptionScales =
  atomicIronScale
  ∷ proteinFerritinScale
  ∷ cellularMacrophageScale
  ∷ tissueHepaticScale
  ∷ peripheralAfferentScale
  ∷ multisensoryIntegrationScale
  ∷ brainObservationScale
  ∷ navigationPolicyScale
  ∷ phenomenalResidualScale
  ∷ []

canonicalCrossScaleRelations : List CrossScaleRelation
canonicalCrossScaleRelations =
  ironHomeostasisAdjacency
  ∷ proteinCellCompatibility
  ∷ immuneCellCompatibility
  ∷ magneticMaterialCompatibility
  ∷ peripheralCentralCandidateTransport
  ∷ multisensoryFusionCandidate
  ∷ brainObservationCompatibility
  ∷ policyConsumptionCompatibility
  ∷ []

canonicalCrossScaleBoundaries : List CrossScaleBoundary
canonicalCrossScaleBoundaries =
  noAtomicIronToSensorDerivation
  ∷ noFerritinToSuperparamagnetismDerivation
  ∷ noImmuneIdentityToMagnetoreceptorSufficiency
  ∷ noAnatomicalProximityToNeuralCodePromotion
  ∷ noPeripheralSignalToBrainStateRecovery
  ∷ noBrainObservationToQualiaRecovery
  ∷ noSensorFusionClosureClaim
  ∷ noSingleCueNavigationClosureClaim
  ∷ []

record AvianMagnetoreceptionCrossScaleBridge : Setω where
  field
    hepaticReceipt :
      Hepatic.HepaticMacrophageMagnetoreceptionReceipt

    hepaticReceiptIsCanonical :
      hepaticReceipt ≡
      Hepatic.canonicalHepaticMacrophageMagnetoreceptionReceipt

    ferritinIronLogic :
      Iron.FerritinophagyLogic

    ferritinIronLogicIsCanonical :
      ferritinIronLogic ≡ Iron.canonicalFerritinophagyLogic

    ferritinMechanismBoundary :
      Iron.ThomasMechanismDepthBoundary

    ferritinMechanismBoundaryIsCanonical :
      ferritinMechanismBoundary ≡
      Iron.canonicalThomasMechanismDepthBoundary

    proteinCellBridge :
      ProteinCell.ProteinHormoneChemistryCellBridge

    proteinCellBridgeIsCanonical :
      proteinCellBridge ≡
      ProteinCell.canonicalProteinHormoneChemistryCellBridge

    cellPhysiologyBridge :
      Cell.CellDifferentiationCommunicationBridge

    cellPhysiologyBridgeIsCanonical :
      cellPhysiologyBridge ≡
      Cell.canonicalCellDifferentiationCommunicationBridge

    embodiedMultisensoryBridge :
      Embodied.EmbodiedMotorMultisensoryBridge

    embodiedMultisensoryBridgeIsCanonical :
      embodiedMultisensoryBridge ≡
      Embodied.canonicalEmbodiedMotorMultisensoryBridge

    neurochemicalBridge :
      Neuro.NeurochemicalTransmissionBridge

    neurochemicalBridgeIsCanonical :
      neurochemicalBridge ≡
      Neuro.canonicalNeurochemicalTransmissionBridge

    brainVocabulary :
      Brain.BrainVocabularySurface

    brainVocabularyIsCanonical :
      brainVocabulary ≡ Brain.brainVocabularySurface

    scales :
      List MagnetoreceptionScale

    scalesAreCanonical :
      scales ≡ canonicalMagnetoreceptionScales

    relations :
      List CrossScaleRelation

    relationsAreCanonical :
      relations ≡ canonicalCrossScaleRelations

    boundaries :
      List CrossScaleBoundary

    boundariesAreCanonical :
      boundaries ≡ canonicalCrossScaleBoundaries

    cellularLanePresent :
      Bool

    cellularLanePresentIsTrue :
      cellularLanePresent ≡ true

    proteinLanePresent :
      Bool

    proteinLanePresentIsTrue :
      proteinLanePresent ≡ true

    ironHomeostasisLanePresent :
      Bool

    ironHomeostasisLanePresentIsTrue :
      ironHomeostasisLanePresent ≡ true

    brainLanePresent :
      Bool

    brainLanePresentIsTrue :
      brainLanePresent ≡ true

    atomicToBehaviorDerivationClaim :
      Bool

    atomicToBehaviorDerivationClaimIsFalse :
      atomicToBehaviorDerivationClaim ≡ false

    receptorToBrainClosureClaim :
      Bool

    receptorToBrainClosureClaimIsFalse :
      receptorToBrainClosureClaim ≡ false

    qualiaRecoveryClaim :
      Bool

    qualiaRecoveryClaimIsFalse :
      qualiaRecoveryClaim ≡ false

    bridgeReading :
      String

open AvianMagnetoreceptionCrossScaleBridge public

canonicalAvianMagnetoreceptionCrossScaleBridge :
  AvianMagnetoreceptionCrossScaleBridge
canonicalAvianMagnetoreceptionCrossScaleBridge =
  record
    { hepaticReceipt =
        Hepatic.canonicalHepaticMacrophageMagnetoreceptionReceipt
    ; hepaticReceiptIsCanonical = refl
    ; ferritinIronLogic =
        Iron.canonicalFerritinophagyLogic
    ; ferritinIronLogicIsCanonical = refl
    ; ferritinMechanismBoundary =
        Iron.canonicalThomasMechanismDepthBoundary
    ; ferritinMechanismBoundaryIsCanonical = refl
    ; proteinCellBridge =
        ProteinCell.canonicalProteinHormoneChemistryCellBridge
    ; proteinCellBridgeIsCanonical = refl
    ; cellPhysiologyBridge =
        Cell.canonicalCellDifferentiationCommunicationBridge
    ; cellPhysiologyBridgeIsCanonical = refl
    ; embodiedMultisensoryBridge =
        Embodied.canonicalEmbodiedMotorMultisensoryBridge
    ; embodiedMultisensoryBridgeIsCanonical = refl
    ; neurochemicalBridge =
        Neuro.canonicalNeurochemicalTransmissionBridge
    ; neurochemicalBridgeIsCanonical = refl
    ; brainVocabulary =
        Brain.brainVocabularySurface
    ; brainVocabularyIsCanonical = refl
    ; scales = canonicalMagnetoreceptionScales
    ; scalesAreCanonical = refl
    ; relations = canonicalCrossScaleRelations
    ; relationsAreCanonical = refl
    ; boundaries = canonicalCrossScaleBoundaries
    ; boundariesAreCanonical = refl
    ; cellularLanePresent = true
    ; cellularLanePresentIsTrue = refl
    ; proteinLanePresent = true
    ; proteinLanePresentIsTrue = refl
    ; ironHomeostasisLanePresent = true
    ; ironHomeostasisLanePresentIsTrue = refl
    ; brainLanePresent = true
    ; brainLanePresentIsTrue = refl
    ; atomicToBehaviorDerivationClaim = false
    ; atomicToBehaviorDerivationClaimIsFalse = refl
    ; receptorToBrainClosureClaim = false
    ; receptorToBrainClosureClaimIsFalse = refl
    ; qualiaRecoveryClaim = false
    ; qualiaRecoveryClaimIsFalse = refl
    ; bridgeReading =
        "Existing iron-homeostasis, protein/cell, immune physiology, multisensory, neurochemical, and brain owners are cross-linked around the hepatic macrophage receipt without claiming a cross-scale derivation or phenomenal closure."
    }
