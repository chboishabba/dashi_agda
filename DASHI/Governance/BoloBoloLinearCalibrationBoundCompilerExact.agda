module DASHI.Governance.BoloBoloLinearCalibrationBoundCompilerExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Governance.BoloBoloFederationCostComparisonExact as Comparison
import DASHI.Governance.BoloBoloRobustCostBoundsExact as Robust
import DASHI.Governance.BoloBoloPracticalSignificanceExact as Significance

------------------------------------------------------------------------
-- LINEAR CALIBRATION-BOUND COMPILER.
--
-- For the explicit linear candidate
--
--   alpha * removed incidence
--   versus
--   beta * boundary + gamma * delegation + delta * unresolved,
--
-- empirical work may bound counts and per-unit weights separately.  This
-- owner proves the monotone compiler from those primitive bounds to a lower
-- bound on removed-global cost and an upper bound on federation overhead.
-- It does not supply the empirical bounds themselves.
------------------------------------------------------------------------

record LinearCalibrationBounds
  (weights : Comparison.LinearCoordinationWeights)
  (accounting : Comparison.FederationTransformationAccounting) : Set where
  constructor linearCalibrationBounds
  field
    incidenceWeightLower : Nat
    removedEdgesLower : Nat

    boundaryWeightUpper : Nat
    boundaryEdgesUpper : Nat
    delegationWeightUpper : Nat
    delegationEdgesUpper : Nat
    unresolvedWeightUpper : Nat
    unresolvedEdgesUpper : Nat

    incidenceWeightLower≤Actual :
      incidenceWeightLower ≤ Comparison.incidenceWeight weights
    removedEdgesLower≤Actual :
      removedEdgesLower ≤ Comparison.removedGlobalEdges accounting

    actualBoundaryWeight≤Upper :
      Comparison.boundaryWeight weights ≤ boundaryWeightUpper
    actualBoundaryEdges≤Upper :
      Comparison.newBoundaryEdges accounting ≤ boundaryEdgesUpper
    actualDelegationWeight≤Upper :
      Comparison.delegationWeight weights ≤ delegationWeightUpper
    actualDelegationEdges≤Upper :
      Comparison.newDelegationEdges accounting ≤ delegationEdgesUpper
    actualUnresolvedWeight≤Upper :
      Comparison.unresolvedWeight weights ≤ unresolvedWeightUpper
    actualUnresolvedEdges≤Upper :
      Comparison.unresolvedDependencyEdges accounting ≤ unresolvedEdgesUpper

open LinearCalibrationBounds public

removedCostLower :
  ∀ {weights accounting} → LinearCalibrationBounds weights accounting → Nat
removedCostLower bounds =
  incidenceWeightLower bounds * removedEdgesLower bounds

boundaryCostUpper :
  ∀ {weights accounting} → LinearCalibrationBounds weights accounting → Nat
boundaryCostUpper bounds =
  boundaryWeightUpper bounds * boundaryEdgesUpper bounds

delegationCostUpper :
  ∀ {weights accounting} → LinearCalibrationBounds weights accounting → Nat
delegationCostUpper bounds =
  delegationWeightUpper bounds * delegationEdgesUpper bounds

unresolvedCostUpper :
  ∀ {weights accounting} → LinearCalibrationBounds weights accounting → Nat
unresolvedCostUpper bounds =
  unresolvedWeightUpper bounds * unresolvedEdgesUpper bounds

federationOverheadUpper :
  ∀ {weights accounting} → LinearCalibrationBounds weights accounting → Nat
federationOverheadUpper bounds =
  boundaryCostUpper bounds
  + delegationCostUpper bounds
  + unresolvedCostUpper bounds

removedCostLowerSound :
  ∀ {weights accounting} →
  (bounds : LinearCalibrationBounds weights accounting) →
  removedCostLower bounds
  ≤ Comparison.removedGlobalCouplingCost (Comparison.linearCostModel weights accounting)
removedCostLowerSound bounds =
  *-mono-≤
    (incidenceWeightLower≤Actual bounds)
    (removedEdgesLower≤Actual bounds)

boundaryCostUpperSound :
  ∀ {weights accounting} →
  (bounds : LinearCalibrationBounds weights accounting) →
  Comparison.boundaryOverheadCost (Comparison.linearCostModel weights accounting)
  ≤ boundaryCostUpper bounds
boundaryCostUpperSound bounds =
  *-mono-≤
    (actualBoundaryWeight≤Upper bounds)
    (actualBoundaryEdges≤Upper bounds)

delegationCostUpperSound :
  ∀ {weights accounting} →
  (bounds : LinearCalibrationBounds weights accounting) →
  Comparison.delegationOverheadCost (Comparison.linearCostModel weights accounting)
  ≤ delegationCostUpper bounds
delegationCostUpperSound bounds =
  *-mono-≤
    (actualDelegationWeight≤Upper bounds)
    (actualDelegationEdges≤Upper bounds)

unresolvedCostUpperSound :
  ∀ {weights accounting} →
  (bounds : LinearCalibrationBounds weights accounting) →
  Comparison.unresolvedDependencyOverheadCost (Comparison.linearCostModel weights accounting)
  ≤ unresolvedCostUpper bounds
unresolvedCostUpperSound bounds =
  *-mono-≤
    (actualUnresolvedWeight≤Upper bounds)
    (actualUnresolvedEdges≤Upper bounds)

federationOverheadUpperSound :
  ∀ {weights accounting} →
  (bounds : LinearCalibrationBounds weights accounting) →
  Comparison.federationOverhead (Comparison.linearCostModel weights accounting)
  ≤ federationOverheadUpper bounds
federationOverheadUpperSound bounds =
  +-mono-≤
    (+-mono-≤
      (boundaryCostUpperSound bounds)
      (delegationCostUpperSound bounds))
    (unresolvedCostUpperSound bounds)

record LinearBoundWin
  {weights : Comparison.LinearCoordinationWeights}
  {accounting : Comparison.FederationTransformationAccounting}
  (bounds : LinearCalibrationBounds weights accounting) : Set where
  constructor linearBoundWin
  field
    overheadUpperBelowRemovedLower :
      federationOverheadUpper bounds < removedCostLower bounds

open LinearBoundWin public

linearBoundWinImpliesStrictImprovement :
  ∀ {weights accounting} →
  (bounds : LinearCalibrationBounds weights accounting) →
  LinearBoundWin bounds →
  Robust.StrictOrderImprovement (Comparison.linearCostModel weights accounting)
linearBoundWinImpliesStrictImprovement {weights} {accounting} bounds witness =
  +-monoˡ-<
    (Comparison.retainedCost (Comparison.linearCostModel weights accounting))
    (<-≤-trans
      (≤-<-trans
        (federationOverheadUpperSound bounds)
        (overheadUpperBelowRemovedLower witness))
      (removedCostLowerSound bounds))

record LinearMeaningfulBoundWin
  {weights : Comparison.LinearCoordinationWeights}
  {accounting : Comparison.FederationTransformationAccounting}
  (threshold : Nat)
  (bounds : LinearCalibrationBounds weights accounting) : Set where
  constructor linearMeaningfulBoundWin
  field
    overheadUpperPlusThresholdBelowRemovedLower :
      federationOverheadUpper bounds + suc threshold
      < removedCostLower bounds

open LinearMeaningfulBoundWin public

linearMeaningfulBoundWinImpliesMeaningfulImprovement :
  ∀ {weights accounting threshold} →
  (bounds : LinearCalibrationBounds weights accounting) →
  LinearMeaningfulBoundWin threshold bounds →
  Significance.MeaningfulOrderImprovement
    threshold
    (Comparison.linearCostModel weights accounting)
linearMeaningfulBoundWinImpliesMeaningfulImprovement
  {weights} {accounting} {threshold} bounds witness =
  +-monoˡ-<
    (Comparison.retainedCost (Comparison.linearCostModel weights accounting))
    (<-≤-trans
      (≤-<-trans
        (+-mono-≤
          (federationOverheadUpperSound bounds)
          ≤-refl)
        (overheadUpperPlusThresholdBelowRemovedLower witness))
      (removedCostLowerSound bounds))

------------------------------------------------------------------------
-- Synthetic exercise only.
------------------------------------------------------------------------

syntheticLinearBoundWeights : Comparison.LinearCoordinationWeights
syntheticLinearBoundWeights = Comparison.linearCoordinationWeights 1 0 0 0

syntheticLinearBoundAccounting : Comparison.FederationTransformationAccounting
syntheticLinearBoundAccounting =
  Comparison.federationTransformationAccounting 43 40 3 0 0 0 refl

syntheticLinearBoundModel : Comparison.CounterfactualCoordinationCostModel
syntheticLinearBoundModel =
  Comparison.linearCostModel syntheticLinearBoundWeights syntheticLinearBoundAccounting

syntheticLinearCalibrationBounds :
  LinearCalibrationBounds syntheticLinearBoundWeights syntheticLinearBoundAccounting
syntheticLinearCalibrationBounds =
  linearCalibrationBounds
    1 3
    0 0 0 0 0 0
    ≤-refl ≤-refl
    ≤-refl ≤-refl ≤-refl ≤-refl ≤-refl ≤-refl

syntheticLinearBoundWin : LinearBoundWin syntheticLinearCalibrationBounds
syntheticLinearBoundWin = linearBoundWin (s≤s z≤n)

syntheticLinearStrictImprovement : Robust.StrictOrderImprovement syntheticLinearBoundModel
syntheticLinearStrictImprovement =
  linearBoundWinImpliesStrictImprovement
    syntheticLinearCalibrationBounds
    syntheticLinearBoundWin

syntheticLinearMeaningfulBoundWin :
  LinearMeaningfulBoundWin 1 syntheticLinearCalibrationBounds
syntheticLinearMeaningfulBoundWin = linearMeaningfulBoundWin ≤-refl

syntheticLinearMeaningfulImprovement :
  Significance.MeaningfulOrderImprovement 1 syntheticLinearBoundModel
syntheticLinearMeaningfulImprovement =
  linearMeaningfulBoundWinImpliesMeaningfulImprovement
    syntheticLinearCalibrationBounds
    syntheticLinearMeaningfulBoundWin

------------------------------------------------------------------------
-- Attribution / interpretation boundary.
------------------------------------------------------------------------

record LinearCalibrationCompilerBoundary : Set where
  constructor linearCalibrationCompilerBoundary
  field
    countAndWeightBoundsCompileMonotonically : Bool
    weightBoundsQuotedFromBoloBolo : Bool
    sourcePopulationNumbersBecomePerUnitCosts : Bool
    owsLexicalCountsAutomaticallyBecomeEventCounts : Bool
    observableCountsAutomaticallyIdentifyCausalCostWeights : Bool
    compiledMeaningfulWinCreatesPoliticalLegitimacy : Bool

open LinearCalibrationCompilerBoundary public

canonicalLinearCalibrationCompilerBoundary : LinearCalibrationCompilerBoundary
canonicalLinearCalibrationCompilerBoundary =
  linearCalibrationCompilerBoundary true false false false false false

canonicalLinearCalibrationBoundCompilerReceipt : GenericReceipt.GenericReceipt
canonicalLinearCalibrationBoundCompilerReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "bolo'bolo linear calibration bound compiler"
    "DASHI.Governance.BoloBoloLinearCalibrationBoundCompilerExact"
    "removedCostLowerSound / federationOverheadUpperSound / linearMeaningfulBoundWinImpliesMeaningfulImprovement"
    "proves the monotone bridge from separately justified lower bounds on removed incidence and incidence weight plus upper bounds on boundary/delegation/unresolved counts and weights into conservative cost bounds for the explicit linear bolo counterfactual, including a predeclared meaningful-margin criterion"
    "the compiler supplies no empirical count semantics or weights: p.m. population numbers are not per-unit costs, OWS lexical markers are not automatically event counts, observable counts do not identify causal cost coefficients, and a compiled coordination result creates no political legitimacy"
    "agda -i . DASHI/Governance/BoloBoloLinearCalibrationBoundCompilerRegression.agda"
