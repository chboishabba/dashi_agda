module DASHI.Governance.BoloBoloPracticalSignificanceExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Governance.BoloBoloFederationCostComparisonExact as Comparison
import DASHI.Governance.BoloBoloRobustCostBoundsExact as Robust

------------------------------------------------------------------------
-- PRACTICAL-SIGNIFICANCE GATE.
--
-- A mathematically strict win may be arbitrarily small.  Comparative
-- promotion therefore needs a predeclared minimum meaningful coordination
-- margin rather than silently treating any epsilon-scale advantage as
-- substantively important.
------------------------------------------------------------------------

MeaningfulOrderImprovement :
  Nat → Comparison.CounterfactualCoordinationCostModel → Set
MeaningfulOrderImprovement threshold model =
  Comparison.federatedCoordinationCost model + suc threshold
  < Comparison.globalCoordinationCost model

MeaningfulOrderLoss :
  Nat → Comparison.CounterfactualCoordinationCostModel → Set
MeaningfulOrderLoss threshold model =
  Comparison.globalCoordinationCost model + suc threshold
  < Comparison.federatedCoordinationCost model

record RobustMeaningfulWin
  {model : Comparison.CounterfactualCoordinationCostModel}
  (threshold : Nat)
  (bounds : Robust.CostIntervalBounds model) : Set where
  constructor robustMeaningfulWin
  field
    overheadUpperPlusThresholdBelowRemovedLower :
      Robust.overheadUpper bounds + suc threshold
      < Robust.removedLower bounds

open RobustMeaningfulWin public

record RobustMeaningfulLoss
  {model : Comparison.CounterfactualCoordinationCostModel}
  (threshold : Nat)
  (bounds : Robust.CostIntervalBounds model) : Set where
  constructor robustMeaningfulLoss
  field
    removedUpperPlusThresholdBelowOverheadLower :
      Robust.removedUpper bounds + suc threshold
      < Robust.overheadLower bounds

open RobustMeaningfulLoss public

robustMeaningfulWinImpliesMargin :
  ∀ {model threshold} →
  (bounds : Robust.CostIntervalBounds model) →
  RobustMeaningfulWin threshold bounds →
  MeaningfulOrderImprovement threshold model
robustMeaningfulWinImpliesMargin {model} {threshold} bounds witness =
  +-monoˡ-<
    (Comparison.retainedCost model)
    (<-≤-trans
      (≤-<-trans
        (+-mono-≤
          (Robust.actualOverhead≤Upper bounds)
          ≤-refl)
        (overheadUpperPlusThresholdBelowRemovedLower witness))
      (Robust.removedLower≤Actual bounds))

robustMeaningfulLossImpliesMargin :
  ∀ {model threshold} →
  (bounds : Robust.CostIntervalBounds model) →
  RobustMeaningfulLoss threshold bounds →
  MeaningfulOrderLoss threshold model
robustMeaningfulLossImpliesMargin {model} {threshold} bounds witness =
  +-monoˡ-<
    (Comparison.retainedCost model)
    (<-≤-trans
      (≤-<-trans
        (+-mono-≤
          (Robust.actualRemoved≤Upper bounds)
          ≤-refl)
        (removedUpperPlusThresholdBelowOverheadLower witness))
      (Robust.overheadLower≤Actual bounds))

------------------------------------------------------------------------
-- Synthetic exercise only.
------------------------------------------------------------------------

syntheticMeaningfulModel : Comparison.CounterfactualCoordinationCostModel
syntheticMeaningfulModel =
  Comparison.counterfactualCoordinationCostModel 40 3 0 0 0

syntheticMeaningfulBounds : Robust.CostIntervalBounds syntheticMeaningfulModel
syntheticMeaningfulBounds =
  Robust.costIntervalBounds 3 3 0 0 ≤-refl ≤-refl ≤-refl ≤-refl

syntheticMeaningfulThreshold : Nat
syntheticMeaningfulThreshold = 1

syntheticRobustMeaningfulWin :
  RobustMeaningfulWin syntheticMeaningfulThreshold syntheticMeaningfulBounds
syntheticRobustMeaningfulWin = robustMeaningfulWin ≤-refl

syntheticMeaningfulOrderImprovement :
  MeaningfulOrderImprovement syntheticMeaningfulThreshold syntheticMeaningfulModel
syntheticMeaningfulOrderImprovement =
  robustMeaningfulWinImpliesMargin
    syntheticMeaningfulBounds
    syntheticRobustMeaningfulWin

------------------------------------------------------------------------
-- Interpretation boundary.
------------------------------------------------------------------------

record PracticalSignificanceBoundary : Set where
  constructor practicalSignificanceBoundary
  field
    meaningfulThresholdMustBePredeclared : Bool
    anyStrictWinAutomaticallyCountsAsMeaningful : Bool
    thresholdQuotedFromBoloBolo : Bool
    thresholdMayBeChosenAfterSeeingTargetOutcome : Bool
    meaningfulCoordinationWinCreatesUniversalPoliticalOptimality : Bool
    meaningfulCoordinationLossRefutesEveryNestedGovernanceVariant : Bool

open PracticalSignificanceBoundary public

canonicalPracticalSignificanceBoundary : PracticalSignificanceBoundary
canonicalPracticalSignificanceBoundary =
  practicalSignificanceBoundary true false false false false false

canonicalPracticalSignificanceReceipt : GenericReceipt.GenericReceipt
canonicalPracticalSignificanceReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "bolo'bolo minimum meaningful coordination margin"
    "DASHI.Governance.BoloBoloPracticalSignificanceExact"
    "robustMeaningfulWinImpliesMargin / robustMeaningfulLossImpliesMargin / canonicalPracticalSignificanceBoundary"
    "strengthens the robust interval comparison by requiring a predeclared minimum meaningful coordination margin before a win or loss is treated as substantively material; conservative separated bounds then certify that margin for every compatible model"
    "the threshold is DASHI analysis design rather than a p.m. source claim, may not be selected after inspecting target outcomes, and even a meaningful coordination advantage creates neither universal political optimality nor legitimacy"
    "agda -i . DASHI/Governance/BoloBoloPracticalSignificanceRegression.agda"
