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
-- This owner refines the cross-kingdom AP comparison into the typed flow
--
--   anaesthetic
--     -> channel/current perturbation
--     -> membrane-potential trajectory
--     -> threshold / propagation state
--     -> lineage-specific behavioural endpoint.
--
-- The quantities are SI typed, but this module deliberately does not invent
-- numerical thresholds, conductances, kinetic parameters or dose-response
-- curves. Concrete experiments must supply those receipts.
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

------------------------------------------------------------------------
-- A quantitative electrical trace. Voltage, current density, and propagation
-- speed remain dimensioned quantities rather than untyped scalar labels.
------------------------------------------------------------------------

record ExcitabilityTrace : Set₁ where
  constructor excitabilityTrace
  field
    State : Set
    voltageScale : SI.DecimalScale
    currentDensityScale : SI.DecimalScale
    propagationVelocityScale : SI.DecimalScale

    membraneVoltage :
      State → SI.Quantity SI.Voltage voltageScale
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
    exposedThreshold :
      thresholdStatus exposed ≡ thresholdCrossingSuppressed
    recoveredThreshold :
      thresholdStatus recovered ≡ thresholdRecovered

    baselinePropagation :
      propagationStatus baseline ≡ AP.propagates
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

------------------------------------------------------------------------
-- Lineage realizations share the observable quantity types but retain their
-- own electrodiffusion application, mechanism receipts, and endpoint mapping.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Forward comparison: same typed measurement ladder, different realizations.
------------------------------------------------------------------------

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
    sharedPropagationVelocityDimensionWitness : sharedPropagationVelocityDimension

    quantityComparisonProtocolReference : String
    scaleConversionProtocolReference : String
    crossLineageExperimentReference : String

open CrossKingdomExcitabilityForwardWeld public

------------------------------------------------------------------------
-- Reverse BIDI audit: observations constrain hypotheses but do not uniquely
-- recover the hidden molecular target or a phenomenological state.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Full BIDI object. Forward state transitions and backward attribution audit
-- are carried together so a behavioural endpoint cannot silently be promoted
-- into a stronger causal or consciousness claim.
------------------------------------------------------------------------

record CrossKingdomAnaestheticExcitabilityBidi : Set₁ where
  constructor crossKingdomAnaestheticExcitabilityBidi
  field
    actionPotentialComparison : AP.CrossKingdomActionPotentialBidi
    forwardWeld : CrossKingdomExcitabilityForwardWeld
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

------------------------------------------------------------------------
-- Constructor-level non-collapse results.
------------------------------------------------------------------------

ionChannelAndNetworkTargetsDistinct :
  ionChannelTarget ≡ networkIntegrationTarget → ⊥
ionChannelAndNetworkTargetsDistinct ()

plantAndAnimalSuppressedBehavioursDistinct :
  plantMovementSuppressed ≡ animalMotorResponseSuppressed → ⊥
plantAndAnimalSuppressedBehavioursDistinct ()

thresholdSuppressionAndRecoveryDistinct :
  thresholdCrossingSuppressed ≡ thresholdRecovered → ⊥
thresholdSuppressionAndRecoveryDistinct ()

------------------------------------------------------------------------
-- The error-model seam is deliberate. A future empirical owner can attach
-- intervals / posterior candidate weights / calibration error to these exact
-- observables without changing the biological claim structure.
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
