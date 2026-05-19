module DASHI.Physics.Closure.BrainConnectomeFMRIObservationQuotient where

open import Agda.Primitive using (Set; Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Brain / perception empirical observation quotient.
--
-- This module refines the perception lane from a direct
--
--   phase orbit class -> fMRI
--
-- story into the more testable chain:
--
--   phase orbit class
--   -> neural state initialization
--   -> connectome-constrained processing
--   -> laminar / high-resolution fMRI readout
--   -> behavioral report
--
-- It is an empirical target surface, not evidence that the fMRI bridge has
-- already been validated.

data TernaryNeuralState : Set where
  inactive :
    TernaryNeuralState

  neutral :
    TernaryNeuralState

  active :
    TernaryNeuralState

data KluverFormConstant : Set where
  tunnel :
    KluverFormConstant

  spiral :
    KluverFormConstant

  lattice :
    KluverFormConstant

  cobweb :
    KluverFormConstant

data TernaryGateClass : Set where
  belowNegativeThreshold :
    TernaryGateClass

  withinVoidBand :
    TernaryGateClass

  abovePositiveThreshold :
    TernaryGateClass

data BrainObservationFirstMissing : Set where
  missingConnectomeDatasetReceipt :
    BrainObservationFirstMissing

  missingNeuralTransitionCalibration :
    BrainObservationFirstMissing

  missingLaminarFMRIProtocolReceipt :
    BrainObservationFirstMissing

  missingPhaseOrbitStimulusProtocol :
    BrainObservationFirstMissing

  missingBehavioralReportBinding :
    BrainObservationFirstMissing

  missingSeparationMetricAndThreshold :
    BrainObservationFirstMissing

  missingEmpiricalComparisonRun :
    BrainObservationFirstMissing

record ConnectomeCarrier : Setω where
  field
    NeuralUnit :
      Set

    Edge :
      Set

    Weight :
      Set

    LayerRegionScale :
      Set

    source target :
      Edge →
      NeuralUnit

    edgeAdmits :
      NeuralUnit →
      NeuralUnit →
      Set

    weight :
      Edge →
      Weight

    nodeLayer :
      NeuralUnit →
      LayerRegionScale

    weightedAdjacency :
      NeuralUnit →
      NeuralUnit →
      Weight

    carrierNotation :
      String

    layerRegionScaleMeaning :
      String

    zeroWeightMeaning :
      String

open ConnectomeCarrier public

record TernaryNeuronalStateCarrier
  (C : ConnectomeCarrier) : Setω where
  field
    NeuralState :
      Set

    stateAt :
      NeuralState →
      ConnectomeCarrier.NeuralUnit C →
      TernaryNeuralState

    activeMeaning :
      String

    neutralMeaning :
      String

    inactiveMeaning :
      String

open TernaryNeuronalStateCarrier public

record ConnectomeConstrainedTransition
  (C : ConnectomeCarrier)
  (N : TernaryNeuronalStateCarrier C) : Setω where
  field
    ExternalDrive :
      Set

    LocalField :
      Set

    Threshold :
      Set

    localField :
      ExternalDrive →
      TernaryNeuronalStateCarrier.NeuralState N →
      ConnectomeCarrier.NeuralUnit C →
      LocalField

    ternaryGate :
      LocalField →
      TernaryGateClass

    gateState :
      TernaryGateClass →
      TernaryNeuralState

    transition :
      ExternalDrive →
      TernaryNeuronalStateCarrier.NeuralState N →
      TernaryNeuronalStateCarrier.NeuralState N

    transitionUsesOnlyAdmittedEdges :
      ExternalDrive →
      TernaryNeuronalStateCarrier.NeuralState N →
      Set

    transitionPointwiseGateLaw :
      ExternalDrive →
      TernaryNeuronalStateCarrier.NeuralState N →
      ConnectomeCarrier.NeuralUnit C →
      Set

    thresholdConvention :
      String

    transitionLawName :
      String

open ConnectomeConstrainedTransition public

record MDLProcessingEnergy
  (C : ConnectomeCarrier)
  (N : TernaryNeuronalStateCarrier C) : Setω where
  field
    Complexity :
      Set

    _≤C_ :
      Complexity →
      Complexity →
      Set

    Observation :
      Set

    stateComplexity :
      TernaryNeuronalStateCarrier.NeuralState N →
      Complexity

    observationResidual :
      Observation →
      TernaryNeuronalStateCarrier.NeuralState N →
      Complexity

    unsupportedConnectomePenalty :
      TernaryNeuronalStateCarrier.NeuralState N →
      Complexity

    deltaC :
      Observation →
      TernaryNeuronalStateCarrier.NeuralState N →
      Complexity

    deltaCDecomposes :
      Observation →
      TernaryNeuronalStateCarrier.NeuralState N →
      Set

    mdlDescent :
      (obs : Observation) →
      TernaryNeuronalStateCarrier.NeuralState N →
      TernaryNeuronalStateCarrier.NeuralState N →
      Set

    mdlDescentSound :
      (obs : Observation) →
      (before after :
        TernaryNeuronalStateCarrier.NeuralState N) →
      mdlDescent obs before after →
      deltaC obs after ≤C deltaC obs before

    unsupportedActivityPenaltyLaw :
      String

open MDLProcessingEnergy public

record ConnectomeSymmetryQuotient
  (C : ConnectomeCarrier)
  (N : TernaryNeuronalStateCarrier C) : Setω where
  field
    ConnectomeSymmetry :
      Set

    actNode :
      ConnectomeSymmetry →
      ConnectomeCarrier.NeuralUnit C →
      ConnectomeCarrier.NeuralUnit C

    preservesWeightedAdjacency :
      ConnectomeSymmetry →
      Set

    actState :
      ConnectomeSymmetry →
      TernaryNeuronalStateCarrier.NeuralState N →
      TernaryNeuronalStateCarrier.NeuralState N

    equivalentProcessingState :
      TernaryNeuronalStateCarrier.NeuralState N →
      TernaryNeuronalStateCarrier.NeuralState N →
      Set

    equivalentRefl :
      (state : TernaryNeuronalStateCarrier.NeuralState N) →
      equivalentProcessingState state state

    equivalentSym :
      (left right : TernaryNeuronalStateCarrier.NeuralState N) →
      equivalentProcessingState left right →
      equivalentProcessingState right left

    equivalentTrans :
      (left middle right : TernaryNeuronalStateCarrier.NeuralState N) →
      equivalentProcessingState left middle →
      equivalentProcessingState middle right →
      equivalentProcessingState left right

    quotientCarrier :
      Set

    classOfState :
      TernaryNeuronalStateCarrier.NeuralState N →
      quotientCarrier

    quotientName :
      String

open ConnectomeSymmetryQuotient public

record ProcessingOrbitQuotient
  (C : ConnectomeCarrier)
  (N : TernaryNeuronalStateCarrier C)
  (T : ConnectomeConstrainedTransition C N) : Setω where
  field
    ProcessingOrbit :
      Set

    iterate :
      ConnectomeConstrainedTransition.ExternalDrive T →
      Nat →
      TernaryNeuronalStateCarrier.NeuralState N →
      TernaryNeuronalStateCarrier.NeuralState N

    orbit :
      ConnectomeConstrainedTransition.ExternalDrive T →
      TernaryNeuronalStateCarrier.NeuralState N →
      ProcessingOrbit

    fixedPoint :
      TernaryNeuronalStateCarrier.NeuralState N →
      Set

    periodicAttractor :
      Nat →
      TernaryNeuronalStateCarrier.NeuralState N →
      Set

    quotientByConnectomeSymmetry :
      ProcessingOrbit →
      Set

open ProcessingOrbitQuotient public

record BrainDASHIObject : Setω where
  field
    Connectome :
      Set

    NeuralUnit :
      Set

    Edge :
      Set

    Weight :
      Set

    NeuralState :
      Set

    Stimulus :
      Set

    ProcessingOrbit :
      Set

    Readout :
      Set

    BehaviorReport :
      Set

    structuralEdge :
      Connectome →
      NeuralUnit →
      NeuralUnit →
      Set

    connectionWeight :
      Connectome →
      NeuralUnit →
      NeuralUnit →
      Weight

    stateAt :
      NeuralState →
      NeuralUnit →
      TernaryNeuralState

    transition :
      Connectome →
      Stimulus →
      NeuralState →
      NeuralState

    processingOrbit :
      Connectome →
      Stimulus →
      NeuralState →
      ProcessingOrbit

    admissibleByConnectome :
      Connectome →
      NeuralState →
      NeuralState →
      Set

    mdlDescent :
      Connectome →
      NeuralState →
      NeuralState →
      Set

    observationQuotient :
      ProcessingOrbit →
      Readout

    behaviorQuotient :
      Readout →
      BehaviorReport

open BrainDASHIObject public

record FMRIObservationQuotient : Setω where
  field
    Cortex :
      Set

    Time :
      Set

    BoldSignal :
      Set

    LayerProfile :
      Set

    ColumnPattern :
      Set

    OrientationMap :
      Set

    RetinotopicGeometry :
      Set

    TemporalCoherence :
      Set

    BOLD :
      Cortex →
      Time →
      BoldSignal

    layerProfile :
      BoldSignal →
      LayerProfile

    columnPattern :
      BoldSignal →
      ColumnPattern

    orientationMap :
      BoldSignal →
      OrientationMap

    retinotopicGeometry :
      BoldSignal →
      RetinotopicGeometry

    temporalCoherence :
      BoldSignal →
      TemporalCoherence

open FMRIObservationQuotient public

record KluverFMRIComparisonTarget : Setω where
  field
    PhaseCarrier :
      Set

    PhaseOrbitClass :
      Set

    BrainState :
      Set

    FMRIReadout :
      Set

    Distance :
      Set

    kappa :
      PhaseCarrier →
      KluverFormConstant

    initializeBrainState :
      PhaseCarrier →
      BrainState

    readout :
      BrainState →
      FMRIReadout

    readoutDistance :
      FMRIReadout →
      FMRIReadout →
      Distance

    sameOrbitSmallDistance :
      PhaseCarrier →
      PhaseCarrier →
      Set

    differentOrbitSeparated :
      PhaseCarrier →
      PhaseCarrier →
      Set

open KluverFMRIComparisonTarget public

record ObservedProcessingQuotient
  (C : ConnectomeCarrier)
  (N : TernaryNeuronalStateCarrier C) : Setω where
  field
    ActiveRegion :
      Set

    LayerProfile :
      Set

    DirectionalFlow :
      Set

    OscillatoryPhase :
      Set

    TaskOutput :
      Set

    activeRegion :
      TernaryNeuronalStateCarrier.NeuralState N →
      ActiveRegion

    layerProfile :
      TernaryNeuronalStateCarrier.NeuralState N →
      LayerProfile

    directionalFlow :
      TernaryNeuronalStateCarrier.NeuralState N →
      DirectionalFlow

    oscillatoryPhase :
      TernaryNeuronalStateCarrier.NeuralState N →
      OscillatoryPhase

    taskOutput :
      TernaryNeuronalStateCarrier.NeuralState N →
      TaskOutput

    coarseBOLDCollapsesLayerSign :
      String

    laminarReadoutPreservesTernarySignTarget :
      String

open ObservedProcessingQuotient public

record DASHIBrainBridge : Setω where
  field
    connectome :
      ConnectomeCarrier

    neuronalState :
      TernaryNeuronalStateCarrier connectome

    transition :
      ConnectomeConstrainedTransition connectome neuronalState

    processingEnergy :
      MDLProcessingEnergy connectome neuronalState

    symmetryQuotient :
      ConnectomeSymmetryQuotient connectome neuronalState

    orbitQuotient :
      ProcessingOrbitQuotient connectome neuronalState transition

    observedQuotient :
      ObservedProcessingQuotient connectome neuronalState

    legacyBrainDASHIObject :
      BrainDASHIObject

    fmriObservationQuotient :
      FMRIObservationQuotient

    kluverComparisonTarget :
      KluverFMRIComparisonTarget

    FMRIReadout :
      Set

    BOLDField :
      Set

    ObservedBOLD :
      Set

    FormConstantClass :
      Set

    readout :
      TernaryNeuronalStateCarrier.NeuralState neuronalState →
      FMRIReadout

    readoutFactorsThroughLayerProfile :
      TernaryNeuronalStateCarrier.NeuralState neuronalState →
      Set

    percept :
      FMRIReadout →
      FormConstantClass

    bridgeApproxObserved :
      (drive : ConnectomeConstrainedTransition.ExternalDrive transition) →
      (steps : Nat) →
      (initial :
        TernaryNeuronalStateCarrier.NeuralState neuronalState) →
      ObservedBOLD →
      Set

    inverseObservationProblem :
      ObservedBOLD →
      Set

    bridgeRespectsSymmetryQuotient :
      (left right :
        TernaryNeuronalStateCarrier.NeuralState neuronalState) →
      ConnectomeSymmetryQuotient.equivalentProcessingState
        symmetryQuotient left right →
      Set

    laminarResolveIsKeyConstraint :
      String

open DASHIBrainBridge public

record BrainConnectomeFMRIObservationBoundary : Set where
  field
    status :
      String

    pipeline :
      List String

    dashiBrainObject :
      String

    connectomeRole :
      String

    processingRole :
      String

    fMRIReadoutRole :
      String

    behavioralReportRole :
      String

    formalBrainCarrier :
      String

    transitionLaw :
      String

    mdlProcessingEnergy :
      String

    connectomeSymmetryQuotient :
      String

    laminarResolveConstraint :
      String

    empiricalTest :
      List String

    highResolutionFMRIIsObservationChannel :
      Bool

    highResolutionFMRIIsObservationChannelIsTrue :
      highResolutionFMRIIsObservationChannel ≡ true

    empiricalValidationClosed :
      Bool

    exactFirstMissing :
      List BrainObservationFirstMissing

    allowedClaim :
      List String

    forbiddenClaim :
      List String

open BrainConnectomeFMRIObservationBoundary public

canonicalBrainConnectomeFMRIObservationBoundary :
  BrainConnectomeFMRIObservationBoundary
canonicalBrainConnectomeFMRIObservationBoundary =
  record
    { status =
        "observation quotient target only; non-promoting"
    ; pipeline =
        "phase orbit class"
        ∷ "neural state initialization"
        ∷ "connectome-constrained processing"
        ∷ "laminar / high-resolution fMRI readout"
        ∷ "behavioral report"
        ∷ []
    ; dashiBrainObject =
        "B = (C, N, P, O), with C structural connectome, N neural/microcircuit state, P processing transition, O observed readout"
    ; connectomeRole =
        "connectome supplies admissibility constraints for neural transitions; it constrains but does not uniquely determine function"
    ; processingRole =
        "processing is modeled as a connectome-constrained transition with MDL / prediction-error / energy descent"
    ; fMRIReadoutRole =
        "high-resolution or laminar fMRI is the macroscopic observation quotient for layer profile, column pattern, orientation map, retinotopic geometry, and temporal coherence"
    ; behavioralReportRole =
        "behavioral report is the external label paired with the fMRI readout and phase-orbit class"
    ; formalBrainCarrier =
        "X_brain = (V, E, W, sigma), with C = (V, E, W, Lambda), sigma_t : V -> {-1, 0, +1}"
    ; transitionLaw =
        "T_C is a connectome-constrained ternary threshold transition; transition support must be contained in admitted anatomical edges"
    ; mdlProcessingEnergy =
        "delta_C(sigma) = state complexity + observation residual + unsupported-connectome penalty; admissible processing descends delta_C"
    ; connectomeSymmetryQuotient =
        "processing content is represented up to connectome automorphisms preserving weighted adjacency"
    ; laminarResolveConstraint =
        "laminar readout must factor through layer profile rather than collapsing directly to a coarse regional scalar"
    ; empiricalTest =
        "same Kluver orbit class should have small fMRI readout distance under the frozen metric"
        ∷ "different Kluver orbit classes should be separated by the frozen fMRI readout metric"
        ∷ "laminar fMRI should preserve a sign-sensitive layer-profile quotient that coarse BOLD collapses"
        ∷ "the comparison must be receipt-bound to stimulus protocol, connectome source, fMRI acquisition, preprocessing, metric, and behavioral report"
        ∷ []
    ; highResolutionFMRIIsObservationChannel =
        true
    ; highResolutionFMRIIsObservationChannelIsTrue =
        refl
    ; empiricalValidationClosed =
        false
    ; exactFirstMissing =
        missingConnectomeDatasetReceipt
        ∷ missingNeuralTransitionCalibration
        ∷ missingLaminarFMRIProtocolReceipt
        ∷ missingPhaseOrbitStimulusProtocol
        ∷ missingBehavioralReportBinding
        ∷ missingSeparationMetricAndThreshold
        ∷ missingEmpiricalComparisonRun
        ∷ []
    ; allowedClaim =
        "high-resolution fMRI is a suitable macroscopic observation quotient target for the perception lane"
        ∷ "the empirical bridge should run through connectome-constrained neural processing, not direct form-constant-to-fMRI identity"
        ∷ "Kluver classes can be tested as phase-orbit classes with fMRI and behavioral readout separation criteria"
        ∷ []
    ; forbiddenClaim =
        "no fMRI dataset validates the Kluver bridge in this module"
        ∷ "no claim is made that connectome structure uniquely determines neural processing"
        ∷ "no consciousness, cognition, or perception closure follows from this observation target"
        ∷ "no empirical promotion is allowed without a frozen dataset, protocol, metric, and comparison receipt"
        ∷ []
    }
