module DASHI.Analysis.BishopOriginalFiniteNormalizedEndpointComparisonExact where

------------------------------------------------------------------------
-- P0.05: CONSUME THE ACTUAL ORIGINAL P0.03 QUOTIENT MODULUS IN
-- EVERY CELL OF THE PREVIOUSLY PROVED NORMALIZED SOURCE TELESCOPE.
--
-- For N, source mesh 0<=v_j<=r<1, and the *actual* source F_N,
-- let B_N(r,h) be the constructed P0.03 stagewise bound. Then
--
-- |G_N(v_m)-G_N(v_0)| <= SUM(j<m) [inv(1-v_j)*inv(1-v_(j+1))
--   * |h_j|*(|v_j^N F_N(v_j)|
--     + |1-v_j|*|F_N(v_j)|*B_N(r,h_j))].
--
-- All terms are the original Bishop finite LOG-EXP objects.
-- This is the real source-level finite comparison, not merely
-- an interface requiring an unspecified uniform error witness.
-- A stage-independent power majorant and mesh refinement remain.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
import Real as R
import RealProperties as RP

import DASHI.Analysis.BishopOriginalNegativeLogFiniteWeightedMeshRecurrenceExact as Mesh
import DASHI.Analysis.BishopOriginalNormalizedFiniteMeshEndpointExact as Endpoint
import DASHI.Analysis.BishopOriginalNegativeLogCrossWeightedIncrementExact as Cross
import DASHI.Analysis.BishopOriginalFiniteLogExpStagewiseUniformDefectExact as Defect
import DASHI.Analysis.BishopOriginalFiniteLogExpQuotientDefectSplitExact as Split
import DASHI.Analysis.BishopOriginalNegativeLogExpFiniteStageLimitExact as Finite
import DASHI.Analysis.BishopOriginalFactorIncrementFiniteTelescopeExact as Walk
import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as Gap

sourceNormalizedCellComparisonBudget :
  (stage : Nat) (radius : R.ℝ) →
  (steps : Nat → R.ℝ) →
  (receipts : (j : Nat) →
    Gap.BishopUnitIntervalRatio (Mesh.sourceVertex steps j)) →
  Nat → R.ℝ
sourceNormalizedCellComparisonBudget stage radius steps receipts j =
  let
    x = Mesh.sourceVertex steps j
    h = steps j
    f = Finite.originalNegativeLogFiniteExponential x stage
    pairInv = R._*_
      (Gap.oneMinusInverse (receipts j))
      (Gap.oneMinusInverse (receipts (suc j)))
    forcing = Cross.sourceODEForcing stage x
    b = Defect.sourceOriginalUniformErrorBudget stage radius h
  in
  R._*_
    pairInv
    (R._*_
      (R.∣ h ∣)
      (R._+_
        (R.∣ forcing ∣)
        (R._*_
          (R.∣ Cross.oneMinus x ∣)
          (R._*_ (R.∣ f ∣) b)))))

originalNormalizedMeshCellConsumesUniformDefect :
  (stage : Nat) (radius : R.ℝ) →
  (steps : Nat → R.ℝ) →
  (receipts : (j : Nat) →
    Gap.BishopUnitIntervalRatio (Mesh.sourceVertex steps j)) →
  (inside : (j : Nat) →
    R._≤_ (Mesh.sourceVertex steps j) radius) →
  (j : Nat) →
  R._≤_
    (R.∣ Endpoint.sourceNormalizedMeshResidualCell
      stage steps receipts j ∣)
    (sourceNormalizedCellComparisonBudget
      stage radius steps receipts j)
originalNormalizedMeshCellConsumesUniformDefect
    stage radius steps receipts inside j =
  let
    x = Mesh.sourceVertex steps j
    h = steps j
    f = Finite.originalNegativeLogFiniteExponential x stage
    w = Cross.oneMinus x
    force = Cross.sourceODEForcing stage x
    d = Split.sourceOriginalErrorSlopeDefect stage x h
    b = Defect.sourceOriginalUniformErrorBudget stage radius h
    pair = R._*_
      (Gap.oneMinusInverse (receipts j))
      (Gap.oneMinusInverse (receipts (suc j)))
    originalResidual = R._+_ force (R._*_ w d)
    xNN = Gap.ratioNonnegativeWitness (receipts j)
    yNN = Gap.ratioNonnegativeWitness (receipts (suc j))
    defectBound =
      Defect.originalFiniteLogExpStagewiseUniformDefectWithFactor
        stage radius x h xNN yNN (inside j) (inside (suc j))
    correctionBelow =
      RP.≤-respˡ-≃
        (RP.∣x*y∣≃∣x∣*∣y∣ w d)
        (RP.*-monoˡ-≤-nonNeg
          defectBound
          (RP.nonNeg∣x∣ w))
    residualBelow =
      RP.≤-trans
        (RP.∣x+y∣≤∣x∣+∣y∣ force (R._*_ w d))
        (RP.+-mono-≤ RP.≤-refl correctionBelow)
    pairNN = RP.nonNegx,y⇒nonNegx*y
      (Gap.oneMinusInverseNonnegative (receipts j))
      (Gap.oneMinusInverseNonnegative (receipts (suc j)))
    absCellFactor =
      RP.≃-trans
        (RP.∣x*y∣≃∣x∣*∣y∣ pair (R._*_ h originalResidual))
        (RP.*-cong
          (RP.nonNegx⇒∣x∣≃x pairNN)
          (RP.∣x*y∣≃∣x∣*∣y∣ h originalResidual))
    upper =
      RP.*-monoˡ-≤-nonNeg
        (RP.*-monoˡ-≤-nonNeg
          residualBelow
          (RP.nonNeg∣x∣ h))
        pairNN
  in
  RP.≤-respˡ-≃ absCellFactor upper

originalBishopFiniteSumPointwiseMonotone :
  (left right : Nat → R.ℝ) →
  ((j : Nat) → R._≤_ (left j) (right j)) →
  (cells : Nat) →
  R._≤_
    (Walk.sumFinite left cells)
    (Walk.sumFinite right cells)
originalBishopFiniteSumPointwiseMonotone left right bound zero =
  RP.≤-refl
originalBishopFiniteSumPointwiseMonotone left right bound (suc n) =
  RP.+-mono-≤
    (originalBishopFiniteSumPointwiseMonotone left right bound n)
    (bound n)

originalBishopFiniteNormalizedEndpointResidualComparison :
  (stage : Nat) (radius : R.ℝ) →
  (steps : Nat → R.ℝ) →
  (receipts : (j : Nat) →
    Gap.BishopUnitIntervalRatio (Mesh.sourceVertex steps j)) →
  (inside : (j : Nat) →
    R._≤_ (Mesh.sourceVertex steps j) radius) →
  (cells : Nat) →
  R._≤_
    (R.∣ R._-_
      (Endpoint.sourceNormalizedMeshAt stage steps receipts cells)
      (Endpoint.sourceNormalizedMeshAt stage steps receipts zero) ∣)
    (Walk.sumFinite
      (sourceNormalizedCellComparisonBudget stage radius steps receipts)
      cells)
originalBishopFiniteNormalizedEndpointResidualComparison
    stage radius steps receipts inside cells =
  RP.≤-trans
    (Endpoint.originalNormalizedFiniteMeshEndpointAbsoluteBudget
      stage steps receipts cells)
    (originalBishopFiniteSumPointwiseMonotone
      (λ j → R.∣ Endpoint.sourceNormalizedMeshResidualCell
        stage steps receipts j ∣)
      (sourceNormalizedCellComparisonBudget
        stage radius steps receipts)
      (originalNormalizedMeshCellConsumesUniformDefect
        stage radius steps receipts inside)
      cells)
