module DASHI.Governance.BoloBoloIncidenceCompressionCostBridgeExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Governance.BoloBoloIncidenceCompressionExact as Compression
import DASHI.Governance.BoloBoloFederationCostComparisonExact as Comparison

------------------------------------------------------------------------
-- INCIDENCE COMPRESSION -> COUNTERFACTUAL COST ACCOUNTING BRIDGE.
--
-- The topology scenario can audit how many participant-issue incidences are
-- removed by localisation, but it does not determine boundary, delegation, or
-- unresolved-dependency overhead.  Those remain explicit inputs.
------------------------------------------------------------------------

record AuditedIncidenceReduction
  (scenario : Compression.EqualPartitionIncidenceScenario) : Set where
  constructor auditedIncidenceReduction
  field
    removedIncidenceEdges : Nat
    exactCompressionPartition :
      Compression.globalIncidenceEdges scenario
      ≡ Compression.localIncidenceEdges scenario + removedIncidenceEdges

open AuditedIncidenceReduction public

compressionToFederationAccounting :
  ∀ {scenario} →
  AuditedIncidenceReduction scenario →
  Nat → Nat → Nat →
  Comparison.FederationTransformationAccounting
compressionToFederationAccounting {scenario} reduction boundary delegation unresolved =
  Comparison.federationTransformationAccounting
    (Compression.globalIncidenceEdges scenario)
    (Compression.localIncidenceEdges scenario)
    (removedIncidenceEdges reduction)
    boundary
    delegation
    unresolved
    (exactCompressionPartition reduction)

------------------------------------------------------------------------
-- Closed arithmetic reductions for the source-inspired scenarios.
------------------------------------------------------------------------

kanaLowerReduction :
  AuditedIncidenceReduction Compression.kanaLowerScenario
kanaLowerReduction = auditedIncidenceReduction 5700 refl

kanaUpperReduction :
  AuditedIncidenceReduction Compression.kanaUpperScenario
kanaUpperReduction = auditedIncidenceReduction 11400 refl

tegaTenReduction :
  AuditedIncidenceReduction Compression.tegaTenBoloScenario
tegaTenReduction = auditedIncidenceReduction 45000 refl

tegaTwentyReduction :
  AuditedIncidenceReduction Compression.tegaTwentyBoloScenario
tegaTwentyReduction = auditedIncidenceReduction 190000 refl

------------------------------------------------------------------------
-- Attribution / interpretation boundary.
------------------------------------------------------------------------

record CompressionCostBridgeBoundary : Set where
  constructor compressionCostBridgeBoundary
  field
    topologyReductionCanPopulateRemovedEdgeCoordinate : Bool
    federationOverheadSuppliedSeparately : Bool
    incidenceReductionAutomaticallyEqualsCoordinationCostReduction : Bool
    zeroFederationOverheadAssumed : Bool
    sourceArchitectureSuppliesBoundaryOverheadCounts : Bool
    sourceArchitectureSuppliesDelegationOverheadCounts : Bool
    sourceArchitectureSuppliesUnresolvedDependencyCounts : Bool
    bridgeSupportsLaterEmpiricalCalibration : Bool

open CompressionCostBridgeBoundary public

canonicalCompressionCostBridgeBoundary : CompressionCostBridgeBoundary
canonicalCompressionCostBridgeBoundary =
  compressionCostBridgeBoundary
    true
    true
    false
    false
    false
    false
    false
    true

canonicalBoloIncidenceCompressionCostBridgeReceipt : GenericReceipt.GenericReceipt
canonicalBoloIncidenceCompressionCostBridgeReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "bolo incidence-compression to cost-accounting bridge"
    "DASHI.Governance.BoloBoloIncidenceCompressionCostBridgeExact"
    "compressionToFederationAccounting / canonicalCompressionCostBridgeBoundary"
    "turns an explicitly audited global-versus-local incidence partition into the removed-global-edge coordinate required by the federation transformation accounting while leaving boundary, delegation and unresolved-dependency overhead as separate supplied inputs"
    "incidence-edge reduction is not automatically coordination-cost reduction, no zero-overhead assumption is made, and p.m.'s source architecture does not supply the missing federation-overhead counts"
    "agda -i . DASHI/Governance/BoloBoloIncidenceCompressionCostBridgeRegression.agda"
