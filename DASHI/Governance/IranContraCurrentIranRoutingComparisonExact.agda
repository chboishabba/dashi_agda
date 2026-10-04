module DASHI.Governance.IranContraCurrentIranRoutingComparisonExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Governance.IranContraCovertFlowHistoricalMechanismExact as Historical
import DASHI.Governance.PetroleumFinancialRoutingNoncollapseExact as Petroleum

------------------------------------------------------------------------
-- HISTORICAL IRAN/CONTRA vs CURRENT IRAN PETROLEUM/FINANCIAL ROUTING
------------------------------------------------------------------------

record TopologyComparison : Set where
  constructor topology-comparison
  field
    historical : Historical.HistoricalRoutingTopology
    current : Petroleum.RoutingMechanismReceipt
    intermediaryLayerComparable : Bool
    intermediaryLayerComparableIsTrue :
      intermediaryLayerComparable ≡ true
    nonstandardSettlementComparable : Bool
    nonstandardSettlementComparableIsTrue :
      nonstandardSettlementComparable ≡ true
    policyConstraintCircumventionComparable : Bool
    policyConstraintCircumventionComparableIsTrue :
      policyConstraintCircumventionComparable ≡ true
    sameActors : Bool
    sameActorsIsFalse : sameActors ≡ false
    sameLegalStatus : Bool
    sameLegalStatusIsFalse : sameLegalStatus ≡ false
    sameGovernmentControlStructure : Bool
    sameGovernmentControlStructureIsFalse :
      sameGovernmentControlStructure ≡ false
    sameDownstreamUse : Bool
    sameDownstreamUseIsFalse :
      sameDownstreamUse ≡ false
    historicalContinuityEstablished : Bool
    historicalContinuityEstablishedIsFalse :
      historicalContinuityEstablished ≡ false

open TopologyComparison public

canonicalComparison : TopologyComparison
canonicalComparison =
  topology-comparison
    Historical.iranContraTopology
    Petroleum.currentIranBarterReceipt
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl

data SimilarTopologyMeansSameOperation : Set where
data SimilarTopologyMeansSharedActors : Set where
data SimilarTopologyMeansSharedIllegality : Set where
data SimilarTopologyMeansHistoricalLineage : Set where

similarTopologyDoesNotCreateSameOperation :
  SimilarTopologyMeansSameOperation → ⊥
similarTopologyDoesNotCreateSameOperation ()

similarTopologyDoesNotCreateSharedActors :
  SimilarTopologyMeansSharedActors → ⊥
similarTopologyDoesNotCreateSharedActors ()

similarTopologyDoesNotCreateSharedIllegality :
  SimilarTopologyMeansSharedIllegality → ⊥
similarTopologyDoesNotCreateSharedIllegality ()

similarTopologyDoesNotCreateHistoricalLineage :
  SimilarTopologyMeansHistoricalLineage → ⊥
similarTopologyDoesNotCreateHistoricalLineage ()
