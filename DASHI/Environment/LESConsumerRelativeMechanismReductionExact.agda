module DASHI.Environment.LESConsumerRelativeMechanismReductionExact where

open import DASHI.Core.Prelude

import DASHI.Core.ConsumerRelativeReductionKernelExact as Reduction
import DASHI.Core.PredictionEnvelopeExact as Envelope
import DASHI.Environment.LESDomainBasisBidiFrontierExact as Basis

------------------------------------------------------------------------
-- REPOSITORY-NATIVE LES ADAPTER
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
-- A reduced code can be consumer-safe without being a mechanistic realization.
-- The latter receives an explicit commuting witness.
------------------------------------------------------------------------

record LESMechanismRealizationWitness
    (mechanism : Basis.DomainMechanismSocket)
    (rom : MechanismReduction mechanism) : Set₁ where
  constructor lesMechanismRealizationWitness
  field
    TargetMechanism : Set
    targetMechanism : Basis.State mechanism → TargetMechanism
    realization : Reduction.ReductionRealizationWitness rom targetMechanism
    realizationAuthorityReference : String
    validationReference : String

open LESMechanismRealizationWitness public

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
-- Intervention semantics are deliberately separate from passive observation.
------------------------------------------------------------------------

record LESInterventionReduction
    (mechanism : Basis.DomainMechanismSocket)
    (rom : MechanismReduction mechanism) : Set₁ where
  constructor lesInterventionReduction
  field
    compatible : Reduction.InterventionCompatibleReduction rom
    interventionAuthorityReference : String
    manipulatedMechanismReference : String
    counterfactualComparisonReference : String
    validationReference : String

open LESInterventionReduction public

LESHistorySensitiveFuture : Basis.DomainMechanismSocket → Set
LESHistorySensitiveFuture mechanism =
  Reduction.HistorySensitiveFutureWitness
    (Basis.evolve mechanism)
    (Basis.observe mechanism)

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

------------------------------------------------------------------------
-- Cheap-model falsification before escalation: if one candidate code collapses
-- two states whose declared future consumer separates, the candidate is not a
-- safe ROM for that consumer/action language.
------------------------------------------------------------------------

record LESCandidateReductionFailure
    (mechanism : Basis.DomainMechanismSocket) : Set₁ where
  constructor lesCandidateReductionFailure
  field
    CandidateCode : Set
    candidate : Basis.State mechanism → CandidateCode
    failure : Reduction.CandidateReductionFailure
      (Basis.evolve mechanism)
      (Basis.observe mechanism)
      candidate
    rejectedReductionReference : String
    nextFidelityReference : String

open LESCandidateReductionFailure public

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
    consumerSafetyAutomaticallyProvesMechanismRealization : Bool
    consumerSafetyAutomaticallyProvesMechanismRealizationIsFalse :
      consumerSafetyAutomaticallyProvesMechanismRealization ≡ false
    failedCheapReductionShouldBeForcedToFit : Bool
    failedCheapReductionShouldBeForcedToFitIsFalse :
      failedCheapReductionShouldBeForcedToFit ≡ false
    symmetryIsOptionalAndMustBeWitnessed : Bool
    symmetryIsOptionalAndMustBeWitnessedIsTrue :
      symmetryIsOptionalAndMustBeWitnessed ≡ true

open LESConsumerReductionBoundary public

canonicalLESConsumerReductionBoundary : LESConsumerReductionBoundary
canonicalLESConsumerReductionBoundary =
  lesConsumerReductionBoundary
    false refl false refl false refl false refl false refl false refl false refl true refl
