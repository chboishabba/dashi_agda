module DASHI.Biology.CrossKingdomAnaestheticExcitabilityFlowBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Biology.CrossKingdomAnaestheticActionBidiExact as Anaesthesia
import DASHI.Biology.CrossKingdomActionPotentialAnaestheticBidiExact as AP
import DASHI.Physics.Electromagnetism.PoissonNernstPlanckElectrodiffusionExact as PNP
import DASHI.Physics.Units.SI as SI

------------------------------------------------------------------------
-- QUANTITATIVE ANAESTHETIC EXCITABILITY FLOW: BIDI WELD
--
--   anaesthetic
--     -> channel/current perturbation
--     -> membrane-potential trajectory
--     -> threshold / propagation state
--     -> lineage-specific behavioural endpoint.
--
-- Quantities are SI typed. This module does not invent numerical thresholds,
-- conductances, kinetic parameters or dose-response curves; concrete
-- experiments must supply those receipts.
--
-- SOURCE CONTINUITY
-- Yokawa et al. 2018. DOI: 10.1093/aob/mcx155.
-- Scherzer et al. 2022. DOI: 10.1016/j.cub.2022.08.051.
-- Hedrich 2023. DOI: 10.1111/nph.19113.
-- Kelz & Mashour 2019. DOI: 10.1016/j.cub.2019.09.071.
------------------------------------------------------------------------

data PerturbationTarget : Set where
  ionChannelTarget
  membraneTarget
  protonPumpTarget
  synapticTarget
  networkIntegrationTarget
  unresolvedTarget
  : PerturbationTarget

data ThresholdStatus : Set where
  belowThreshold
  thresholdReached
  thresholdCrossingSuppressed
  thresholdRecovered
  : ThresholdStatus

data BehaviouralResponse : Set where
  plantMovementAvailable
  plantMovementSuppressed
  plantMovementRecovered
  animalMotorResponseAvailable
  animalMotorResponseSuppressed
  animalMotorResponseRecovered
  : BehaviouralResponse

data AttributionStatus : Set where
  identified
  boundedCandidate
  unresolved
  : AttributionStatus

data ObservationLayer : Set where
  currentObservation
  voltageObservation
  thresholdObservation
  propagationObservation
  behaviourObservation
  : ObservationLayer

record ExcitabilityTrace : Set₁ where
  constructor excitabilityTrace
  field
    State : Set
    voltageScale : SI.DecimalScale
    currentDensityScale : SI.DecimalScale
    propagationVelocityScale : SI.DecimalScale
    membraneVoltage : State → SI.Quantity SI.Voltage voltageScale
    transmembraneCurrentDensity :
      State → SI.Quantity SI.CurrentDensity currentDensityScale
    propagationVelocity :
      State → SI.Quantity SI.Velocity propagationVelocityScale
    thresholdStatus : State → ThresholdStatus
    propagationStatus : State → AP.PropagationStatus
    baseline : State
    exposed : State
    recovered : State
    baselineThreshold : thresholdStatus baseline ≡ thresholdReached
    exposedThreshold : thresholdStatus exposed ≡ thresholdCrossingSuppressed
    recoveredThreshold : thresholdStatus recovered ≡ thresholdRecovered
    baselinePropagation : propagationStatus baseline ≡ AP.propagates
    exposedPropagation :
      propagationStatus exposed ≡ AP.propagationSuppressed
    recoveredPropagation :
      propagationStatus recovered ≡ AP.recoveredPropagation
    voltageMeasurementReference : String
    currentMeasurementReference : String
    propagationMeasurementReference : String
    thresholdDefinitionReference : String
    recoveryDefinitionReference : String

open ExcitabilityTrace public

record PlantExcitabilityRealization : Set₁ where
  constructor plantExcitabilityRealization
  field
    pnpApplication : PNP.ElectrodiffusionApplicationReceipt
    applicationIsExcitablePlantMembrane :
      PNP.application pnpApplication ≡ PNP.plantExcitableMembrane
    architecture : AP.PlantActionPotentialArchitecture
    trace : ExcitabilityTrace
    perturbationTarget : PerturbationTarget
    perturbationAttribution : AttributionStatus
    behaviouralResponse : State trace → BehaviouralResponse
    exposedBehaviourSuppressed :
      behaviouralResponse (exposed trace) ≡ plantMovementSuppressed
    recoveredBehaviour :
      behaviouralResponse (recovered trace) ≡ plantMovementRecovered
    channelCurrentCouplingReference : String
    voltageThresholdCouplingReference : String
    propagationMovementCouplingReference : String
    anaestheticDoseExposureReference : String
    experimentalValidationReference : String

open PlantExcitabilityRealization public

record AnimalExcitabilityRealization : Set₁ where
  constructor animalExcitabilityRealization
  field
    pnpApplication : PNP.ElectrodiffusionApplicationReceipt
    applicationIsNeuronalMembrane :
      PNP.application pnpApplication ≡ PNP.neuronalMembrane
    architecture : AP.AnimalActionPotentialArchitecture
    trace : ExcitabilityTrace
    perturbationTarget : PerturbationTarget
    perturbationAttribution : AttributionStatus
    behaviouralResponse : State trace → BehaviouralResponse
    exposedBehaviourSuppressed :
      behaviouralResponse (exposed trace) ≡ animalMotorResponseSuppressed
    recoveredBehaviour :
      behaviouralResponse (recovered trace) ≡ animalMotorResponseRecovered
    channelCurrentCouplingReference : String
    voltageThresholdCouplingReference : String
    propagationMotorCouplingReference : String
    anaestheticDoseExposureReference : String
    experimentalValidationReference : String

open AnimalExcitabilityRealization public

record CrossKingdomExcitabilityForwardWeld : Set₁ where
  constructor crossKingdomExcitabilityForwardWeld
  field
    plant : PlantExcitabilityRealization
    animal : AnimalExcitabilityRealization
    sharedVoltageDimension : Set
    sharedVoltageDimensionWitness : sharedVoltageDimension
    sharedCurrentDensityDimension : Set
    sharedCurrentDensityDimensionWitness : sharedCurrentDensityDimension
    sharedPropagationVelocityDimension : Set
    sharedPropagationVelocityDimensionWitness :
      sharedPropagationVelocityDimension
    quantityComparisonProtocolReference : String
    scaleConversionProtocolReference : String
    crossLineageExperimentReference : String

open CrossKingdomExcitabilityForwardWeld public

------------------------------------------------------------------------
-- Observation hierarchy. Every adjacent link needs its own empirical receipt;
-- a downstream observation is not installed as an inverse of the upstream map.
------------------------------------------------------------------------

record ExcitabilityObservationChain : Set₁ where
  constructor excitabilityObservationChain
  field
    MechanismState : Set
    CurrentState : Set
    VoltageState : Set
    ThresholdState : Set
    PropagationState : Set
    BehaviourState : Set
    mechanismToCurrent : MechanismState → CurrentState
    currentToVoltage : CurrentState → VoltageState
    voltageToThreshold : VoltageState → ThresholdState
    thresholdToPropagation : ThresholdState → PropagationState
    propagationToBehaviour : PropagationState → BehaviourState
    mechanismCurrentReceipt : String
    currentVoltageReceipt : String
    voltageThresholdReceipt : String
    thresholdPropagationReceipt : String
    propagationBehaviourReceipt : String

open ExcitabilityObservationChain public

record ExcitabilityBackwardAudit : Set where
  constructor excitabilityBackwardAudit
  field
    suppressedPropagationUniquelyIdentifiesChannelTarget : Bool
    suppressedPropagationUniquelyIdentifiesChannelTargetIsFalse :
      suppressedPropagationUniquelyIdentifiesChannelTarget ≡ false
    suppressedMovementUniquelyIdentifiesElectricalMechanism : Bool
    suppressedMovementUniquelyIdentifiesElectricalMechanismIsFalse :
      suppressedMovementUniquelyIdentifiesElectricalMechanism ≡ false
    sameVoltageDimensionImpliesSameVoltageTrajectory : Bool
    sameVoltageDimensionImpliesSameVoltageTrajectoryIsFalse :
      sameVoltageDimensionImpliesSameVoltageTrajectory ≡ false
    sameCurrentDimensionImpliesSameChannelInventory : Bool
    sameCurrentDimensionImpliesSameChannelInventoryIsFalse :
      sameCurrentDimensionImpliesSameChannelInventory ≡ false
    recoveryOfPlantMovementEstablishesPriorPlantUnconsciousness : Bool
    recoveryOfPlantMovementEstablishesPriorPlantUnconsciousnessIsFalse :
      recoveryOfPlantMovementEstablishesPriorPlantUnconsciousness ≡ false
    quantitativeTraceCanBoundMechanismCandidates : Bool
    quantitativeTraceCanBoundMechanismCandidatesIsTrue :
      quantitativeTraceCanBoundMechanismCandidates ≡ true

canonicalExcitabilityBackwardAudit : ExcitabilityBackwardAudit
canonicalExcitabilityBackwardAudit =
  excitabilityBackwardAudit
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl

record CrossKingdomAnaestheticExcitabilityBidi : Set₁ where
  constructor crossKingdomAnaestheticExcitabilityBidi
  field
    actionPotentialComparison : AP.CrossKingdomActionPotentialBidi
    forwardWeld : CrossKingdomExcitabilityForwardWeld
    observationChain : ExcitabilityObservationChain
    backwardAudit : ExcitabilityBackwardAudit
    plantEndpoint : Anaesthesia.PlantAnaestheticEndpoint
    plantEndpointIsActionPotentialSuppression :
      plantEndpoint ≡ Anaesthesia.plantActionPotentialSuppressed
    animalEndpoint : Anaesthesia.AnimalAnaestheticEndpoint
    animalEndpointIsNeuronalExcitabilityAltered :
      animalEndpoint ≡ Anaesthesia.neuronalExcitabilityAltered
    forwardBackwardCommonExperimentReference : String
    uncertaintyOrErrorModelReference : String
    mechanismCandidateSetReference : String

open CrossKingdomAnaestheticExcitabilityBidi public

ionChannelAndNetworkTargetsDistinct :
  ionChannelTarget ≡ networkIntegrationTarget → ⊥
ionChannelAndNetworkTargetsDistinct ()

plantAndAnimalSuppressedBehavioursDistinct :
  plantMovementSuppressed ≡ animalMotorResponseSuppressed → ⊥
plantAndAnimalSuppressedBehavioursDistinct ()

thresholdSuppressionAndRecoveryDistinct :
  thresholdCrossingSuppressed ≡ thresholdRecovered → ⊥
thresholdSuppressionAndRecoveryDistinct ()

currentAndBehaviourObservationLayersDistinct :
  currentObservation ≡ behaviourObservation → ⊥
currentAndBehaviourObservationLayersDistinct ()

------------------------------------------------------------------------
-- Error-model seam. Future empirical owners can attach intervals, posterior
-- candidate weights, or calibration error without changing the claim graph.
------------------------------------------------------------------------

record ExcitabilityUncertaintyReceipt : Set₁ where
  constructor excitabilityUncertaintyReceipt
  field
    Measurement : Set
    ErrorBound : Set
    measurement : Measurement
    errorBound : ErrorBound
    calibrationReference : String
    uncertaintyModelReference : String
    admissibleMechanismSetReference : String

open ExcitabilityUncertaintyReceipt public
