module DASHI.Biology.CrossModalityFunctionalObservationBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Biology.DrosophilaMaleCNSEffectorObservationBridge as Fly
import DASHI.Physics.Closure.BrainConnectomeFMRIObservationQuotient as Brain

------------------------------------------------------------------------
-- Cross-modality bridge.
--
-- Calcium, voltage, electrophysiology and BOLD are treated as distinct lossy
-- observation maps of latent neural/vascular state.  The bridge permits
-- calibrated comparison and transport without asserting modality identity.
------------------------------------------------------------------------

data CrossModalityBoundary : Set where
  noCalciumEqualsBOLDClaim : CrossModalityBoundary
  noVoltageEqualsBOLDClaim : CrossModalityBoundary
  noEphysEqualsBOLDClaim : CrossModalityBoundary
  noUniversalNeurovascularMapClaim : CrossModalityBoundary
  noFlyBOLDPhysiologyTransferWithoutReceipt : CrossModalityBoundary
  noObservationEqualsLatentStateClaim : CrossModalityBoundary

logothetisSource : Fly.ScientificSourceReceipt
logothetisSource =
  Fly.scientificSourceReceipt
    "Logothetis, Pauls, Augath, Trinath, Oeltermann"
    "Neurophysiological investigation of the basis of the fMRI signal"
    "DOI:10.1038/35084005"
    "Simultaneous intracortical electrophysiology and BOLD fMRI in monkey visual cortex; supports an empirical neural-to-BOLD bridge rather than signal identity."

ubaghsSource : Fly.ScientificSourceReceipt
ubaghsSource =
  Fly.scientificSourceReceipt
    "Ubaghs et al."
    "Simultaneous single-cell calcium imaging of neuronal population activity and brain-wide BOLD fMRI"
    "DOI:10.1038/s41592-026-03154-2"
    "Simultaneous cellular calcium and brain-wide BOLD measurements in awake mice; supports spatially varying calcium/BOLD coupling."

crossModalitySources : List Fly.ScientificSourceReceipt
crossModalitySources =
  Fly.wholeBrainCalciumSource
  ∷ logothetisSource
  ∷ ubaghsSource
  ∷ []

record LatentFunctionalState : Set₁ where
  field
    NeuralPopulationState : Set
    VascularState : Set
    MetabolicState : Set
    Time : Set

open LatentFunctionalState public

record ModalityObservationModel (L : LatentFunctionalState) : Set₁ where
  field
    CalciumObservation : Set
    VoltageObservation : Set
    EphysObservation : Set
    BOLDObservation : Set

    calciumReadout : NeuralPopulationState L → CalciumObservation
    voltageReadout : NeuralPopulationState L → VoltageObservation
    ephysReadout : NeuralPopulationState L → EphysObservation

    neurovascularCoupling :
      NeuralPopulationState L →
      VascularState L →
      MetabolicState L →
      VascularState L

    boldReadout :
      NeuralPopulationState L →
      VascularState L →
      MetabolicState L →
      BOLDObservation

    calciumLossy : Bool
    voltageLossy : Bool
    ephysLossy : Bool
    boldLossy : Bool

    couplingCalibrated : Bool
    couplingReceipt : Fly.ScientificSourceReceipt

open ModalityObservationModel public

record CrossModalityComparison
    {L : LatentFunctionalState}
    (M : ModalityObservationModel L) : Set₁ where
  field
    ComparisonResidual : Set

    calciumToBOLDResidual :
      CalciumObservation M →
      BOLDObservation M →
      ComparisonResidual

    voltageToBOLDResidual :
      VoltageObservation M →
      BOLDObservation M →
      ComparisonResidual

    ephysToBOLDResidual :
      EphysObservation M →
      BOLDObservation M →
      ComparisonResidual

    residualAdmissible : ComparisonResidual → Set

    modalitiesIdentified : Bool
    modalitiesIdentifiedIsFalse : modalitiesIdentified ≡ false

open CrossModalityComparison public

------------------------------------------------------------------------
-- Fly-specific adapter: optical observations can directly validate a MaleCNS
-- latent/dynamical model.  A BOLD arm remains optional and cannot be populated
-- from mammalian neurovascular receipts alone.
------------------------------------------------------------------------

record DrosophilaFunctionalConnectomeAdapter
    (L : LatentFunctionalState)
    (M : ModalityObservationModel L) : Set₁ where
  field
    ConnectomeState : Set
    OpticalObservation : Set
    BehaviourObservation : Set

    connectomeToLatent : ConnectomeState → NeuralPopulationState L
    opticalFromLatent : NeuralPopulationState L → OpticalObservation
    behaviourFromLatent : NeuralPopulationState L → BehaviourObservation

    opticalReceipt : Fly.ScientificSourceReceipt
    connectomeReceipt : Fly.ScientificSourceReceipt

    flyBOLDReceiptPresent : Bool
    flyBOLDReceiptPresentIsFalse : flyBOLDReceiptPresent ≡ false

    mammalianBOLDCalibrationDoesNotPromoteFlyBOLD : Bool
    mammalianBOLDCalibrationDoesNotPromoteFlyBOLDIsTrue :
      mammalianBOLDCalibrationDoesNotPromoteFlyBOLD ≡ true

open DrosophilaFunctionalConnectomeAdapter public

canonicalCrossModalityBoundaries : List CrossModalityBoundary
canonicalCrossModalityBoundaries =
  noCalciumEqualsBOLDClaim
  ∷ noVoltageEqualsBOLDClaim
  ∷ noEphysEqualsBOLDClaim
  ∷ noUniversalNeurovascularMapClaim
  ∷ noFlyBOLDPhysiologyTransferWithoutReceipt
  ∷ noObservationEqualsLatentStateClaim
  ∷ []
