module DASHI.Economics.AIRelationshipDataProviderBoundary2026Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Economics.AIGeometricMarketStressOperator2026Exact as Geometry

------------------------------------------------------------------------
-- EXTERNAL BUSINESS-RELATIONSHIP DATA PROVIDER BOUNDARY
--
-- These products can populate parts of the customer/supplier/partner graph.
-- They do not by themselves provide all capital, debt, guarantee, ownership,
-- revenue-quality or terminal-payer edges required by the full multiplex
-- circular-financing observable.
------------------------------------------------------------------------

spBusinessRelationships : Source.AttributedSource
spBusinessRelationships = Source.mkNoDOISource
  "S&P Global Market Intelligence"
  "Business Relationships Analytics"
  "S&P Global"
  "2026"
  "https://www.spglobal.com/market-intelligence/en/solutions/products/business-relationships-analytics"
  Source.institutionalSource
  "provider documentation reports 600,000+ entities and 1.6 million supplier-customer relationships, mixing disclosed relationships with model-estimated values and supporting network stress analysis"
  Source.publicAttribution

bloombergSupplyChain : Source.AttributedSource
bloombergSupplyChain = Source.mkNoDOISource
  "Bloomberg"
  "Supply Chain"
  "Bloomberg Professional Services"
  "2026"
  "https://professional.bloomberg.com/institutions/corporations/supply-chain/"
  Source.institutionalSource
  "provider documentation reports 500,000+ unique supplier/customer relationships across more than 100,000 public and private companies"
  Source.publicAttribution

factsetSupplyChain : Source.AttributedSource
factsetSupplyChain = Source.mkNoDOISource
  "FactSet"
  "FactSet Supply Chain Relationships"
  "FactSet Marketplace"
  "2026"
  "https://fact-set.com/marketplace/catalog/product/factset-supply-chain-relationships"
  Source.institutionalSource
  "provider documentation exposes customer, supplier, partner and competitor relationships with direct/reverse sourcing and relationship context"
  Source.publicAttribution

record RelationshipDataCapability : Set where
  constructor relationshipDataCapability
  field
    provider : String
    customerSupplierGraph : Bool
    partnerGraph : Bool
    competitorGraph : Bool
    historicalRelationships : Bool
    estimatedMissingValues : Bool
    debtGuaranteeGraphComplete : Bool
    terminalPayerPartitionComplete : Bool
    source : Source.AttributedSource

open RelationshipDataCapability public

spCapability : RelationshipDataCapability
spCapability = relationshipDataCapability
  "S&P Global Business Relationships Analytics"
  true false false true true false false spBusinessRelationships

bloombergCapability : RelationshipDataCapability
bloombergCapability = relationshipDataCapability
  "Bloomberg Supply Chain"
  true false false true false false false bloombergSupplyChain

factsetCapability : RelationshipDataCapability
factsetCapability = relationshipDataCapability
  "FactSet Supply Chain Relationships"
  true true true true false false false factsetSupplyChain

data ProviderCoverageImpliesCompleteEntanglementGraphPermission : Set where
data EstimatedEdgeImpliesAuditedCashFlowPermission : Set where
data SupplierGraphImpliesTerminalPayerPartitionPermission : Set where

providerCoverageDoesNotAutoCloseEntanglementGraph :
  ProviderCoverageImpliesCompleteEntanglementGraphPermission → ⊥
providerCoverageDoesNotAutoCloseEntanglementGraph ()

estimatedEdgeDoesNotAutoBecomeAuditedCashFlow :
  EstimatedEdgeImpliesAuditedCashFlowPermission → ⊥
estimatedEdgeDoesNotAutoBecomeAuditedCashFlow ()

supplierGraphDoesNotAutoCloseTerminalPayerPartition :
  SupplierGraphImpliesTerminalPayerPartitionPermission → ⊥
supplierGraphDoesNotAutoCloseTerminalPayerPartition ()

repoGeometricStressInterface : Set
repoGeometricStressInterface = Geometry.QualitativeJointStress
