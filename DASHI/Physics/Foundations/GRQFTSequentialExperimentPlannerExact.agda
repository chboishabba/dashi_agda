module DASHI.Physics.Foundations.GRQFTSequentialExperimentPlannerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.CommonExperimentRealisationExact as Common
import DASHI.Core.SequentialRelationalExperimentPlannerExact as Sequential
import DASHI.Physics.Foundations.PhysicalTheoryExperimentDiscriminationExact as Physical

------------------------------------------------------------------------
-- SEQUENTIAL GR/QFT EXPERIMENT PLANNING
--
-- Physical candidate theories generally admit sets of possible observations,
-- so the deterministic sensor-tree calculus is too strong here.  This adapter
-- uses the relational planner directly on the existing `Predictions` owner.
--
-- One external experiment language is still required, following the common-
-- metric-variation discipline: different candidate-internal apparatus
-- coordinates do not become the same physical experiment by name alone.
------------------------------------------------------------------------

physicalRelationalSystem :
  ∀ {Theory Observation : Set}
    (common : Common.CommonExperimentRealisation Theory Theory)
    (predicts : Physical.Predictions
      Theory (Common.Experiment common) Observation)
    (cost : Common.Experiment common → Nat)
    (observationReference : Observation → String) →
  Sequential.RelationalExperimentSystem
    Theory (Common.Experiment common) Observation
physicalRelationalSystem common predicts cost observationReference =
  Sequential.relationalExperimentSystem
    predicts
    cost
    (Common.experimentReference common)
    observationReference

record SequentialPhysicalExperimentProgramme : Set₂ where
  constructor sequentialPhysicalExperimentProgramme
  field
    Theory Observation Consumer : Set
    common : Common.CommonExperimentRealisation Theory Theory
    predicts : Physical.Predictions
      Theory (Common.Experiment common) Observation
    experimentCost : Common.Experiment common → Nat
    observationClassificationReference : Observation → String

    live : Theory → Set
    consumer : Theory → Consumer

    system : Sequential.RelationalExperimentSystem
      Theory (Common.Experiment common) Observation
    systemIsPhysicalPredictions :
      Sequential.predicts system ≡ predicts

    plan : Sequential.CertifiedSequentialRelationalPlan
      system consumer live

    physicalCandidate : Physical.FundamentalPhysicalCandidate
    grRecoveryReference :
      Physical.recoversGeneralRelativityRegime physicalCandidate
    qftRecoveryReference :
      Physical.recoversLowEnergyQuantumFieldRegime physicalCandidate

    nuisanceAndSystematicsReference : String
    apparatusAuthorityReference : String
    programmeReference : String

open SequentialPhysicalExperimentProgramme public

------------------------------------------------------------------------
-- Canonical constructor avoids inventing a second prediction relation.
------------------------------------------------------------------------

canonicalSequentialPhysicalExperimentProgramme :
  ∀ {Theory Observation Consumer : Set}
    (common : Common.CommonExperimentRealisation Theory Theory)
    (predicts : Physical.Predictions
      Theory (Common.Experiment common) Observation)
    (experimentCost : Common.Experiment common → Nat)
    (observationReference : Observation → String)
    (live : Theory → Set)
    (consumer : Theory → Consumer)
    (plan : Sequential.CertifiedSequentialRelationalPlan
      (physicalRelationalSystem common predicts experimentCost observationReference)
      consumer live)
    (physicalCandidate : Physical.FundamentalPhysicalCandidate) →
    Physical.recoversGeneralRelativityRegime physicalCandidate →
    Physical.recoversLowEnergyQuantumFieldRegime physicalCandidate →
    String → String → String →
  SequentialPhysicalExperimentProgramme
canonicalSequentialPhysicalExperimentProgramme
    common predicts experimentCost observationReference live consumer plan
    physicalCandidate grRecovery qftRecovery nuisance authority programme =
  sequentialPhysicalExperimentProgramme
    _ _ _
    common predicts experimentCost observationReference
    live consumer
    (physicalRelationalSystem common predicts experimentCost observationReference)
    refl
    plan
    physicalCandidate grRecovery qftRecovery
    nuisance authority programme

------------------------------------------------------------------------
-- Boundary: sequential closure is consumer-relative.  A terminal tree may
-- settle a declared physical prediction or decision while leaving multiple
-- candidate theories alive.  Conversely, completing such a tree does not by
-- itself discharge the physical promotion gate.
------------------------------------------------------------------------

record GRQFTSequentialPlannerBoundary : Set where
  constructor grqftSequentialPlannerBoundary
  field
    everyPhysicalTheoryPredictsOneDeterministicMeasurement : Bool
    everyPhysicalTheoryPredictsOneDeterministicMeasurementIsFalse :
      everyPhysicalTheoryPredictsOneDeterministicMeasurement ≡ false

    experimentChoiceMayDependOnEarlierObservedOutcome : Bool
    experimentChoiceMayDependOnEarlierObservedOutcomeIsTrue :
      experimentChoiceMayDependOnEarlierObservedOutcome ≡ true

    consumerClosureImpliesCandidateTheoryIdentity : Bool
    consumerClosureImpliesCandidateTheoryIdentityIsFalse :
      consumerClosureImpliesCandidateTheoryIdentity ≡ false

    sequentialConsumerClosureCompletesPhysicalPromotion : Bool
    sequentialConsumerClosureCompletesPhysicalPromotionIsFalse :
      sequentialConsumerClosureCompletesPhysicalPromotion ≡ false

canonicalGRQFTSequentialPlannerBoundary : GRQFTSequentialPlannerBoundary
canonicalGRQFTSequentialPlannerBoundary =
  grqftSequentialPlannerBoundary
    false refl true refl false refl false refl
