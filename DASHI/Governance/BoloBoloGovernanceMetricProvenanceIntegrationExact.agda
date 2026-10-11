module DASHI.Governance.BoloBoloGovernanceMetricProvenanceIntegrationExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Governance.BoloBoloCounterfactualEvaluationExact as Evaluation
import DASHI.Governance.BoloBoloGovernanceMetricProvenanceExact as Metric

------------------------------------------------------------------------
-- Thin capstone integration.
--
-- The existing counterfactual evaluation remains the owner of the substantive
-- bolo'bolo structural/empirical frontier.  This module adds the current-master
-- metric-role provenance firewall without duplicating that large record.
------------------------------------------------------------------------

record BoloEvaluationWithMetricProvenance : Set where
  constructor boloEvaluationWithMetricProvenance
  field
    evaluation : Evaluation.BoloCounterfactualEvaluation
    metricProvenanceBoundary : Metric.GovernanceMetricProvenanceBoundary

open BoloEvaluationWithMetricProvenance public

canonicalBoloEvaluationWithMetricProvenance : BoloEvaluationWithMetricProvenance
canonicalBoloEvaluationWithMetricProvenance =
  boloEvaluationWithMetricProvenance
    Evaluation.canonicalBoloCounterfactualEvaluation
    Metric.canonicalGovernanceMetricProvenanceBoundary

record MetricProvenanceIntegrationBoundary : Set where
  constructor metricProvenanceIntegrationBoundary
  field
    metricRoleProvenanceFirewallPaid : Bool
    equalScalarPaysCrossRoleTransport : Bool
    sameScalarComparatorTargetPaysTransfer : Bool
    sameScalarThresholdOutcomePaysPracticalSignificance : Bool
    metricProvenanceCreatesEmpiricalMeasurement : Bool
    metricProvenanceCreatesPoliticalLegitimacy : Bool

open MetricProvenanceIntegrationBoundary public

canonicalMetricProvenanceIntegrationBoundary : MetricProvenanceIntegrationBoundary
canonicalMetricProvenanceIntegrationBoundary =
  metricProvenanceIntegrationBoundary true false false false false false

canonicalMetricProvenanceIntegrationReceipt : GenericReceipt.GenericReceipt
canonicalMetricProvenanceIntegrationReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "bolo'bolo metric-role provenance integration"
    "DASHI.Governance.BoloBoloGovernanceMetricProvenanceIntegrationExact"
    "canonicalBoloEvaluationWithMetricProvenance / canonicalMetricProvenanceIntegrationBoundary"
    "threads the current-master number/role provenance discipline into the persistent adaptive bolo counterfactual so scalar equality cannot discharge role-, unit-, provenance-, transfer- or practical-threshold obligations"
    "this is a representation and calibration firewall only: it creates no target measurement, cost coefficient, interface-capacity observation, practical-significance result, political legitimacy or longitudinal advantage"
    "agda -i . DASHI/Governance/BoloBoloGovernanceMetricProvenanceIntegrationRegression.agda"
