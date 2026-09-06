module DASHI.Biology.DrosophilaMaleCNSEffectorObservationBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Source receipts
--
-- Repository attribution rule: every external scientific source carried by
-- this module records author/consortium, title, and DOI or another stable
-- identifier if no DOI is available.
------------------------------------------------------------------------

record ScientificSourceReceipt : Set where
  constructor scientificSourceReceipt
  field
    authorOrConsortium : String
    title : String
    stableIdentifier : String
    sourceReading : String

open ScientificSourceReceipt public

maleCNSSource : ScientificSourceReceipt
maleCNSSource =
  scientificSourceReceipt
    "Berg et al."
    "Sexual dimorphism in the complete Drosophila male central nervous system connectome"
    "DOI:10.1016/j.cell.2026.08.015"
    "Complete male Drosophila CNS connectome spanning brain and nerve cord; structural sensory-to-motor analysis and male/female synaptic-resolution comparison."

bancEmbodiedControlSource : ScientificSourceReceipt
bancEmbodiedControlSource =
  scientificSourceReceipt
    "Bates et al.; BANC-FlyWire Consortium"
    "Distributed control circuits across a brain-and-cord connectome"
    "DOI:10.1038/s41586-026-10735-w"
    "Brain-and-cord connectome analysis relating sensory neurons, ascending/descending circuits, and effector neurons in embodied control architecture."

wholeBrainCalciumSource : ScientificSourceReceipt
wholeBrainCalciumSource =
  scientificSourceReceipt
    "Gauthey, Lin, Ahmed, Leifer, Murthy, Thiberge et al."
    "High-speed whole-brain imaging in Drosophila"
    "DOI:10.1038/s41467-026-72437-1"
    "Adult behaving-fly whole-brain calcium imaging using light-beads microscopy; functional optical imaging, not BOLD fMRI."

larvalWholeCNSSource : ScientificSourceReceipt
larvalWholeCNSSource =
  scientificSourceReceipt
    "Lemon et al."
    "Whole-central nervous system functional imaging in larval Drosophila"
    "DOI:10.1038/ncomms8924"
    "Whole-CNS functional optical imaging in larval Drosophila."

canonicalSources : List ScientificSourceReceipt
canonicalSources =
  maleCNSSource
  ∷ bancEmbodiedControlSource
  ∷ wholeBrainCalciumSource
  ∷ larvalWholeCNSSource
  ∷ []

------------------------------------------------------------------------
-- Structural CNS carrier and explicit effector continuation.
--
-- The connectome may reach motor / endocrine / visceral efferent neurons,
-- but a structural connectome is not itself a physical effector-state trace.
-- The programme therefore continues across that boundary using separately
-- receipted actuation, biomechanics, and behavioural producers.
------------------------------------------------------------------------

data CNSRole : Set where
  sensoryNeuron : CNSRole
  centralInterneuron : CNSRole
  descendingNeuron : CNSRole
  ascendingNeuron : CNSRole
  vncInterneuron : CNSRole
  motorNeuron : CNSRole
  endocrineEffectorNeuron : CNSRole
  visceralEfferentNeuron : CNSRole

data ObservationModality : Set where
  structuralConnectome : ObservationModality
  opticalCalcium : ObservationModality
  opticalVoltage : ObservationModality
  electrophysiology : ObservationModality
  boldFMRI : ObservationModality
  behaviouralKinematics : ObservationModality
  forceOrContact : ObservationModality

data EffectorKind : Set where
  legMusculature : EffectorKind
  wingMusculature : EffectorKind
  proboscisMusculature : EffectorKind
  abdominalMusculature : EffectorKind
  endocrineTarget : EffectorKind
  visceralTarget : EffectorKind

data BridgeBoundary : Set where
  noConnectomeDeterminesDynamicsClaim : BridgeBoundary
  noMotorNeuronEqualsMotorCommandClaim : BridgeBoundary
  noMotorCommandEqualsEffectorStateClaim : BridgeBoundary
  noEffectorStateEqualsObservedBehaviourClaim : BridgeBoundary
  noROMExactnessWithoutResidualReceipt : BridgeBoundary
  noBOLDFMRIFruitFlyClaimWithoutReceipt : BridgeBoundary
  noIntentOrQualiaRecoveryClaim : BridgeBoundary

record MaleCNSStructuralCarrier : Set₁ where
  field
    NeuralUnit : Set
    Edge : Set
    Weight : Set
    CellType : Set
    Region : Set
    Hemilineage : Set
    Neurotransmitter : Set
    SexCorrespondence : Set

    source target : Edge → NeuralUnit
    weight : Edge → Weight
    role : NeuralUnit → CNSRole
    cellType : NeuralUnit → CellType
    region : NeuralUnit → Region
    hemilineage : NeuralUnit → Hemilineage
    neurotransmitter : NeuralUnit → Neurotransmitter
    sexCorrespondence : NeuralUnit → SexCorrespondence

    structuralReceipt : ScientificSourceReceipt

open MaleCNSStructuralCarrier public

record NeuralToEffectorSurface
    (C : MaleCNSStructuralCarrier) : Set₁ where
  field
    NeuralState : Set
    Stimulus : Set
    MotorCommand : Set
    MotorNeuronDrive : Set
    EffectorState : Set
    BodyState : Set
    BehaviourObservation : Set
    SensoryReturn : Set

    connectomeConstrainedStep : Stimulus → NeuralState → NeuralState
    motorCommandFromNeural : NeuralState → MotorCommand
    motorDriveFromCommand : MotorCommand → MotorNeuronDrive
    effectorFromMotorDrive : MotorNeuronDrive → EffectorState
    bodyFromEffector : EffectorState → BodyState
    observeBehaviour : BodyState → BehaviourObservation
    sensoryReturnFromBody : BodyState → SensoryReturn

    motorDriveUsesStructuralMotorBoundary : MotorNeuronDrive → Set
    actuationReceipt : ScientificSourceReceipt
    biomechanicsReceipt : ScientificSourceReceipt
    behaviourReceipt : ScientificSourceReceipt

open NeuralToEffectorSurface public

------------------------------------------------------------------------
-- SeaMeInIt/ROM x-pollination: reduced effector coordinates are a projection
-- of a full body/effector state, with an explicit residual.  The residual is
-- part of the scientific object and blocks silent exactness promotion.
------------------------------------------------------------------------

record EffectorROM
    {C : MaleCNSStructuralCarrier}
    (E : NeuralToEffectorSurface C) : Set₁ where
  field
    Coefficient : Set
    Residual : Set

    projectEffector : EffectorState E → Coefficient
    reconstructEffector : Coefficient → EffectorState E
    reconstructionResidual : EffectorState E → Residual

    residualAdmissible : Residual → Set
    exactInverseClaim : Bool
    exactInverseClaimIsFalse : exactInverseClaim ≡ false
    romReceipt : String

open EffectorROM public

------------------------------------------------------------------------
-- fMRI/general functional-observation x-pollination.
--
-- fMRI is one member of a modality family.  Drosophila currently has strong
-- whole-brain/whole-CNS functional optical-imaging receipts in this source set.
-- We do not promote those receipts to a literal BOLD-fMRI result.
------------------------------------------------------------------------

record FunctionalObservationQuotient
    {C : MaleCNSStructuralCarrier}
    (E : NeuralToEffectorSurface C) : Set₁ where
  field
    NeuralObservation : Set
    BodyObservation : Set

    neuralModality : ObservationModality
    bodyModality : ObservationModality

    observeNeural : NeuralState E → NeuralObservation
    observeBody : BodyState E → BodyObservation

    neuralObservationIsLossy : Bool
    bodyObservationIsLossy : Bool

    modalityReceipt : ScientificSourceReceipt

open FunctionalObservationQuotient public

record FruitFlyFunctionalImagingBoundary : Set where
  field
    wholeBrainCalciumReceiptPresent : Bool
    wholeBrainCalciumReceiptPresentIsTrue :
      wholeBrainCalciumReceiptPresent ≡ true

    literalBOLDFMRIFruitFlyReceiptPresentInCurrentSourceSet : Bool
    literalBOLDFMRIFruitFlyReceiptPresentInCurrentSourceSetIsFalse :
      literalBOLDFMRIFruitFlyReceiptPresentInCurrentSourceSet ≡ false

    allowedReading : String
    forbiddenReading : String

open FruitFlyFunctionalImagingBoundary public

canonicalFruitFlyFunctionalImagingBoundary :
  FruitFlyFunctionalImagingBoundary
canonicalFruitFlyFunctionalImagingBoundary =
  record
    { wholeBrainCalciumReceiptPresent = true
    ; wholeBrainCalciumReceiptPresentIsTrue = refl
    ; literalBOLDFMRIFruitFlyReceiptPresentInCurrentSourceSet = false
    ; literalBOLDFMRIFruitFlyReceiptPresentInCurrentSourceSetIsFalse = refl
    ; allowedReading =
        "Drosophila has whole-brain and whole-CNS functional optical-imaging receipts; the generic brain observation quotient may be instantiated with optical calcium or other receipted modalities."
    ; forbiddenReading =
        "Do not call optical calcium imaging fruit-fly fMRI or assert a Drosophila BOLD-fMRI result without an explicit source receipt."
    }

------------------------------------------------------------------------
-- Closed-loop embodied experiment object.
------------------------------------------------------------------------

record EmbodiedMaleCNSExperiment : Set₁ where
  field
    connectome : MaleCNSStructuralCarrier
    effectorSurface : NeuralToEffectorSurface connectome
    effectorROM : EffectorROM effectorSurface
    observation : FunctionalObservationQuotient effectorSurface

    SourceState : Set
    TargetState : Set

    sourceState : SourceState
    targetState : TargetState

    sources : List ScientificSourceReceipt
    boundaries : List BridgeBoundary

    structuralToMotorReceipted : Bool
    motorToEffectorReceipted : Bool
    effectorToBehaviourReceipted : Bool

    experimentReading : String

open EmbodiedMaleCNSExperiment public

canonicalBoundaries : List BridgeBoundary
canonicalBoundaries =
  noConnectomeDeterminesDynamicsClaim
  ∷ noMotorNeuronEqualsMotorCommandClaim
  ∷ noMotorCommandEqualsEffectorStateClaim
  ∷ noEffectorStateEqualsObservedBehaviourClaim
  ∷ noROMExactnessWithoutResidualReceipt
  ∷ noBOLDFMRIFruitFlyClaimWithoutReceipt
  ∷ noIntentOrQualiaRecoveryClaim
  ∷ []
