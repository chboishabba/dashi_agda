module DASHI.Governance.BoloBoloPairedExperimentMetricTypingExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Governance.BoloBoloGovernanceMetricProvenanceExact as Metric
import DASHI.Governance.BoloBoloPairedGovernanceExperimentExact as Experiment

------------------------------------------------------------------------
-- ROLE-INDEXED WRAPPER FOR THE PAIRED EXPERIMENT OUTCOME VECTOR.
--
-- `OutcomeVector` intentionally keeps arithmetic-friendly Nat fields.  This
-- owner adds a proof-relevant semantic layer: selected measurements are indexed
-- by their governance metric role and tied by equality to the exact raw field.
-- The wrapper does not manufacture source provenance or empirical values.
------------------------------------------------------------------------

record RoleTypedMetric (role : Metric.GovernanceMetricRole) : Set where
  constructor roleTypedMetric
  field
    scalar : Nat
    unitLabel : String
    provenance : String

open RoleTypedMetric public

record TypedOutcomeVector : Set where
  constructor typedOutcomeVector
  field
    rawOutcome : Experiment.OutcomeVector

    duration : RoleTypedMetric Metric.observedDurationMinutes
    incidence : RoleTypedMetric Metric.incidenceEdgeCount
    capacity : RoleTypedMetric Metric.interfaceCapacity
    peakDemand : RoleTypedMetric Metric.peakBoundaryDemand
    backlog : RoleTypedMetric Metric.backlogCount
    realisedChannels : RoleTypedMetric Metric.realisedCrossGroupChannelCount

    durationMatchesRaw :
      scalar duration ≡ Experiment.durationMinutes rawOutcome
    incidenceMatchesRaw :
      scalar incidence ≡ Experiment.incidenceEdges rawOutcome
    capacityMatchesRaw :
      scalar capacity ≡ Experiment.interfaceCapacity rawOutcome
    peakDemandMatchesRaw :
      scalar peakDemand ≡ Experiment.peakBoundaryDemand rawOutcome
    backlogMatchesRaw :
      scalar backlog ≡ Experiment.interfaceBacklog rawOutcome
    realisedChannelsMatchRaw :
      scalar realisedChannels ≡ Experiment.realisedCrossGroupChannels rawOutcome

open TypedOutcomeVector public

------------------------------------------------------------------------
-- Finite role-separation witnesses inherited from the metric owner.
------------------------------------------------------------------------

durationRoleCannotBecomeCapacityRole :
  Metric.observedDurationMinutes ≡ Metric.interfaceCapacity → ⊥
durationRoleCannotBecomeCapacityRole ()

incidenceRoleCannotBecomePeakDemandRole :
  Metric.incidenceEdgeCount ≡ Metric.peakBoundaryDemand → ⊥
incidenceRoleCannotBecomePeakDemandRole ()

backlogRoleCannotBecomeRealisedChannelRole :
  Metric.backlogCount ≡ Metric.realisedCrossGroupChannelCount → ⊥
backlogRoleCannotBecomeRealisedChannelRole ()

record PairedExperimentMetricTypingBoundary : Set where
  constructor pairedExperimentMetricTypingBoundary
  field
    rawNatFieldsAreSemanticallyInterchangeable : Bool
    measurementProvenanceRequired : Bool
    sameScalarCanPayDifferentRoleWithoutReceipt : Bool
    typedWrapperCreatesEmpiricalObservation : Bool
    typedWrapperCreatesCrossContextTransfer : Bool
    typedWrapperPreservesRawOutcomeIdentity : Bool

open PairedExperimentMetricTypingBoundary public

canonicalPairedExperimentMetricTypingBoundary : PairedExperimentMetricTypingBoundary
canonicalPairedExperimentMetricTypingBoundary =
  pairedExperimentMetricTypingBoundary false true false false false true

canonicalPairedExperimentMetricTypingReceipt : GenericReceipt.GenericReceipt
canonicalPairedExperimentMetricTypingReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "bolo'bolo paired-experiment role-indexed metric typing"
    "DASHI.Governance.BoloBoloPairedExperimentMetricTypingExact"
    "RoleTypedMetric / TypedOutcomeVector / canonicalPairedExperimentMetricTypingBoundary"
    "adds a role-indexed wrapper over the existing paired-governance OutcomeVector and ties duration, incidence, interface capacity, peak boundary demand, backlog and realised-channel measurements back to the exact raw Nat fields by equality, preventing scalar coincidence from erasing metric meaning"
    "the wrapper supplies no empirical observation, source provenance, cross-context transfer, causal coefficient or target result; concrete trials must still populate provenance/units and satisfy the existing experiment and promotion obligations"
    "agda -i . DASHI/Governance/BoloBoloPairedExperimentMetricTypingRegression.agda"
