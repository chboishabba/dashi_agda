module DASHI.Governance.BoloBoloRobustCostBoundsExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Governance.BoloBoloFederationCostComparisonExact as Comparison

------------------------------------------------------------------------
-- ROBUST / PARTIALLY IDENTIFIED BOLO'BOLO COST COMPARISON.
--
-- The exact positive-margin theorem is useful once all costs are identified,
-- but empirical work commonly produces intervals or conservative bounds.
-- This owner therefore proves the stronger practical criterion:
--
--   upper(federation overhead) < lower(removed global cost)
--
-- is sufficient for a strict coordination-cost win for every model compatible
-- with those bounds.  Conversely,
--
--   upper(removed global cost) < lower(federation overhead)
--
-- is sufficient for a strict loss.  Overlapping intervals are intentionally
-- left unresolved rather than converted into a point estimate.
------------------------------------------------------------------------

record CostIntervalBounds
  (model : Comparison.CounterfactualCoordinationCostModel) : Set where
  constructor costIntervalBounds
  field
    removedLower : Nat
    removedUpper : Nat
    overheadLower : Nat
    overheadUpper : Nat

    removedLower≤Actual :
      removedLower ≤ Comparison.removedGlobalCouplingCost model
    actualRemoved≤Upper :
      Comparison.removedGlobalCouplingCost model ≤ removedUpper
    overheadLower≤Actual :
      overheadLower ≤ Comparison.federationOverhead model
    actualOverhead≤Upper :
      Comparison.federationOverhead model ≤ overheadUpper

open CostIntervalBounds public

record RobustWin
  {model : Comparison.CounterfactualCoordinationCostModel}
  (bounds : CostIntervalBounds model) : Set where
  constructor robustWin
  field
    overheadUpperBelowRemovedLower :
      overheadUpper bounds < removedLower bounds

open RobustWin public

record RobustLoss
  {model : Comparison.CounterfactualCoordinationCostModel}
  (bounds : CostIntervalBounds model) : Set where
  constructor robustLoss
  field
    removedUpperBelowOverheadLower :
      removedUpper bounds < overheadLower bounds

open RobustLoss public

StrictOrderImprovement : Comparison.CounterfactualCoordinationCostModel → Set
StrictOrderImprovement model =
  Comparison.federatedCoordinationCost model
  < Comparison.globalCoordinationCost model

StrictOrderLoss : Comparison.CounterfactualCoordinationCostModel → Set
StrictOrderLoss model =
  Comparison.globalCoordinationCost model
  < Comparison.federatedCoordinationCost model

robustWinImpliesRemovedDominates :
  ∀ {model} →
  (bounds : CostIntervalBounds model) →
  RobustWin bounds →
  Comparison.federationOverhead model
  < Comparison.removedGlobalCouplingCost model
robustWinImpliesRemovedDominates bounds witness =
  <-≤-trans
    (≤-<-trans
      (actualOverhead≤Upper bounds)
      (overheadUpperBelowRemovedLower witness))
    (removedLower≤Actual bounds)

robustWinImpliesStrictOrderImprovement :
  ∀ {model} →
  (bounds : CostIntervalBounds model) →
  RobustWin bounds →
  StrictOrderImprovement model
robustWinImpliesStrictOrderImprovement {model} bounds witness =
  +-monoˡ-<
    (Comparison.retainedCost model)
    (robustWinImpliesRemovedDominates bounds witness)

robustLossImpliesRemovedBelowOverhead :
  ∀ {model} →
  (bounds : CostIntervalBounds model) →
  RobustLoss bounds →
  Comparison.removedGlobalCouplingCost model
  < Comparison.federationOverhead model
robustLossImpliesRemovedBelowOverhead bounds witness =
  <-≤-trans
    (≤-<-trans
      (actualRemoved≤Upper bounds)
      (removedUpperBelowOverheadLower witness))
    (overheadLower≤Actual bounds)

robustLossImpliesStrictOrderLoss :
  ∀ {model} →
  (bounds : CostIntervalBounds model) →
  RobustLoss bounds →
  StrictOrderLoss model
robustLossImpliesStrictOrderLoss {model} bounds witness =
  +-monoˡ-<
    (Comparison.retainedCost model)
    (robustLossImpliesRemovedBelowOverhead bounds witness)

------------------------------------------------------------------------
-- Multi-level measurement packet.
--
-- These intervals are evidence targets.  They do not assert that such bounds
-- are presently available; they make explicit which nested terms must be
-- bounded before a robust bolo/kana/tega comparison can be made.
------------------------------------------------------------------------

record NestedCostBoundTargets : Set where
  constructor nestedCostBoundTargets
  field
    removedGlobalLowerBoundRequired : Bool
    boloInterfaceUpperBoundRequired : Bool
    tegaInterfaceUpperBoundRequired : Bool
    widerInterfaceUpperBoundRequired : Bool
    delegationUpperBoundRequired : Bool
    unresolvedDependencyUpperBoundRequired : Bool
    retainedLocalCostCancelsInSameModelComparison : Bool

open NestedCostBoundTargets public

canonicalNestedCostBoundTargets : NestedCostBoundTargets
canonicalNestedCostBoundTargets =
  nestedCostBoundTargets true true true true true true true

------------------------------------------------------------------------
-- Interpretation / attribution firewall.
------------------------------------------------------------------------

record RobustCostBoundary : Set where
  constructor robustCostBoundary
  field
    robustWinUsesRemovedLowerAndOverheadUpper : Bool
    robustLossUsesRemovedUpperAndOverheadLower : Bool
    exactPointIdentificationRequiredForRobustClassification : Bool
    overlappingIntervalsMayRemainIndeterminate : Bool
    occupyDerivedBoundsAutomaticallyTransferToBolo : Bool
    sourcePopulationNumbersBecomeStatisticalConfidenceBounds : Bool
    robustCoordinationWinCreatesPoliticalLegitimacy : Bool
    robustCoordinationWinCreatesEcologicalViability : Bool
    nonlinearOrContextDependentCostsRemainPossible : Bool

open RobustCostBoundary public

canonicalRobustCostBoundary : RobustCostBoundary
canonicalRobustCostBoundary =
  robustCostBoundary
    true
    true
    false
    true
    false
    false
    false
    false
    true

canonicalBoloRobustCostBoundsReceipt : GenericReceipt.GenericReceipt
canonicalBoloRobustCostBoundsReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "bolo'bolo robust partially-identified cost comparison"
    "DASHI.Governance.BoloBoloRobustCostBoundsExact"
    "robustWinImpliesStrictOrderImprovement / robustLossImpliesStrictOrderLoss / canonicalRobustCostBoundary"
    "upgrades the exact-point counterfactual comparison to conservative interval evidence: an upper bound on all federation overhead strictly below a lower bound on removed global-coupling cost certifies a coordination-cost win for every compatible model, while the reverse separated bounds certify a loss"
    "overlapping intervals remain indeterminate; Occupy-derived bounds do not automatically transport to a bolo context, source population figures are not statistical bounds, and even a robust coordination-cost result creates neither legitimacy nor ecological viability"
    "agda -i . DASHI/Governance/BoloBoloRobustCostBoundsRegression.agda"
