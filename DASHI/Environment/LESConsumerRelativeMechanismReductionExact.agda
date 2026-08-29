module DASHI.Environment.LESConsumerRelativeMechanismReductionExact where

open import DASHI.Core.Prelude

import DASHI.Core.ConsumerRelativeReductionKernelExact as Reduction
import DASHI.Core.PredictionEnvelopeExact as Envelope
import DASHI.Environment.LESDomainBasisBidiFrontierExact as Basis

------------------------------------------------------------------------
-- REPOSITORY-NATIVE LES ADAPTER
--
-- The generic reduction kernel lives in DASHI.Core and is intentionally not an
-- environmental special case.  This module only instantiates its questions on
-- an LES DomainMechanismSocket.
------------------------------------------------------------------------

MechanismReduction : Basis.DomainMechanismSocket → Set₁
MechanismReduction mechanism =
  Reduction.ConsumerRelativeReduction
    (Basis.State mechanism)
    (Basis.Control mechanism)
    (Basis.Observation mechanism)

record LESReductionRealization
    (mechanism : Basis.DomainMechanismSocket) : Set₁ where
  constructor lesReductionRealization
  field
    reduction : MechanismReduction mechanism
    sameFineEvolution : Reduction.fineStep reduction ≡ Basis.evolve mechanism
    sameFineObservation : Reduction.fineObserve reduction ≡ Basis.observe mechanism
    discrepancyPreservationReference : String
    applicationScopeReference : String
    validationReference : String

open LESReductionRealization public

------------------------------------------------------------------------
-- Exact active-experiment question.
------------------------------------------------------------------------

record LESExperimentDiscriminator
    (mechanism : Basis.DomainMechanismSocket)
    (rom : MechanismReduction mechanism) : Set₁ where
  constructor lesExperimentDiscriminator
  field
    left right : Basis.State mechanism
    currentlyCollapsed : Reduction.encode rom left ≡ Reduction.encode rom right
    experiment : Basis.Experiment mechanism
    experimentSeparates :
      Basis.experimentObserve mechanism experiment left
      ≡ Basis.experimentObserve mechanism experiment right → ⊥

open LESExperimentDiscriminator public

------------------------------------------------------------------------
-- Prediction-envelope closure remains consumer-relative.  An experiment is
-- valuable when the measured fibre closes the declared prediction, not merely
-- when it produces a numerically different sensor reading.
------------------------------------------------------------------------

record LESMeasurementEnvelopeQuestion
    (mechanism : Basis.DomainMechanismSocket) : Set₁ where
  constructor lesMeasurementEnvelopeQuestion
  field
    Evidence : Set
    Measurement : Set
    Prediction : Set
    compatible : Envelope.Compatible Evidence (Basis.State mechanism)
    measure : Basis.State mechanism → Measurement
    consumer : Basis.State mechanism → Prediction
    currentEvidence : Evidence
    measuredValue : Measurement

  closesEnvelope : Set
  closesEnvelope =
    Envelope.MeasurementClosesEnvelope
      compatible measure consumer (currentEvidence , measuredValue)

open LESMeasurementEnvelopeQuestion public

------------------------------------------------------------------------
-- Online assimilation is exact fibre intersection at this layer.  Weighting,
-- Bayesian semantics or correlated error models can be attached separately.
------------------------------------------------------------------------

record LESAssimilationStep
    (mechanism : Basis.DomainMechanismSocket) : Set₁ where
  constructor lesAssimilationStep
  field
    Evidence : Set
    Measurement : Set
    compatible : Envelope.Compatible Evidence (Basis.State mechanism)
    measure : Basis.State mechanism → Measurement
    priorEvidence : Evidence
    observation : Measurement

  assimilatedCompatible : Basis.State mechanism → Set
  assimilatedCompatible =
    Envelope.MeasuredCompatible compatible measure (priorEvidence , observation)

open LESAssimilationStep public

------------------------------------------------------------------------
-- Mechanistic equifinality.
------------------------------------------------------------------------

record LESMechanismEquifinality
    (mechanism : Basis.DomainMechanismSocket)
    (rom : MechanismReduction mechanism) : Set₁ where
  constructor lesMechanismEquifinality
  field
    MechanismLabel : Set
    mechanismLabel : Basis.State mechanism → MechanismLabel
    left right : Basis.State mechanism
    sameReducedConsumerState : Reduction.encode rom left ≡ Reduction.encode rom right
    distinctMechanism : mechanismLabel left ≡ mechanismLabel right → ⊥

open LESMechanismEquifinality public

------------------------------------------------------------------------
-- A control in DomainMechanismSocket is already an intervention-like state
-- transition.  Consumer safety under arbitrary finite control traces is thus
-- inherited mechanically from the generic reduction theorem.
------------------------------------------------------------------------

controlTraceConsumerSafe :
  (mechanism : Basis.DomainMechanismSocket) →
  (rom : MechanismReduction mechanism) →
  (controls : List (Basis.Control mechanism)) →
  (state : Basis.State mechanism) →
  Reduction.fineObserve rom
    (Reduction.run (Reduction.fineStep rom) controls state)
  ≡ Reduction.reducedObserve rom
    (Reduction.run (Reduction.reducedStep rom) controls
      (Reduction.encode rom state))
controlTraceConsumerSafe mechanism rom = Reduction.consumerFuturePreserved rom

------------------------------------------------------------------------
-- Environmental hysteresis/path dependence is a generic future-separation
-- witness instantiated on the mechanism's native evolution and observation.
------------------------------------------------------------------------

LESHistorySensitiveFuture : Basis.DomainMechanismSocket → Set
LESHistorySensitiveFuture mechanism =
  Reduction.HistorySensitiveFutureWitness
    (Basis.evolve mechanism)
    (Basis.observe mechanism)

------------------------------------------------------------------------
-- Multi-fidelity and spatial-scale aliases.
------------------------------------------------------------------------

record LESFidelityEscalation
    (mechanism : Basis.DomainMechanismSocket)
    (low high : MechanismReduction mechanism) : Set where
  constructor lesFidelityEscalation
  field
    witness : Reduction.FidelityEscalationWitness low high
    escalationReasonReference : String
    costOrLatencyReference : String
    validationReference : String

open LESFidelityEscalation public

record LESScaleSafeAggregation
    (mechanism : Basis.DomainMechanismSocket) : Set₁ where
  constructor lesScaleSafeAggregation
  field
    fineScaleReference : String
    coarseScaleReference : String
    aggregation : Reduction.ScaleSafeReduction
      (Basis.State mechanism)
      (Basis.Control mechanism)
      (Basis.Observation mechanism)
    scaleSupportReference : String
    aggregationValidationReference : String

open LESScaleSafeAggregation public

record LESConsumerReductionBoundary : Set where
  constructor lesConsumerReductionBoundary
  field
    smallReconstructionErrorAloneProvesConsumerSafety : Bool
    smallReconstructionErrorAloneProvesConsumerSafetyIsFalse :
      smallReconstructionErrorAloneProvesConsumerSafety ≡ false

    sameFitImpliesSameMechanism : Bool
    sameFitImpliesSameMechanismIsFalse : sameFitImpliesSameMechanism ≡ false

    extraMeasurementAlwaysAddsInformation : Bool
    extraMeasurementAlwaysAddsInformationIsFalse :
      extraMeasurementAlwaysAddsInformation ≡ false

    spatialAveragingAutomaticallyCommutesWithDynamics : Bool
    spatialAveragingAutomaticallyCommutesWithDynamicsIsFalse :
      spatialAveragingAutomaticallyCommutesWithDynamics ≡ false

    controlConditioningEqualsIntervention : Bool
    controlConditioningEqualsInterventionIsFalse :
      controlConditioningEqualsIntervention ≡ false

    symmetryIsOptionalAndMustBeWitnessed : Bool
    symmetryIsOptionalAndMustBeWitnessedIsTrue :
      symmetryIsOptionalAndMustBeWitnessed ≡ true

open LESConsumerReductionBoundary public

canonicalLESConsumerReductionBoundary : LESConsumerReductionBoundary
canonicalLESConsumerReductionBoundary =
  lesConsumerReductionBoundary
    false refl false refl false refl false refl false refl true refl
