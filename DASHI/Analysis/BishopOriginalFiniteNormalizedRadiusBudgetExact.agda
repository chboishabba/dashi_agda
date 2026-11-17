module DASHI.Analysis.BishopOriginalFiniteNormalizedRadiusBudgetExact where

------------------------------------------------------------------------
-- K04d P0.05: ORIGINAL NORMALIZED MESH WITH A COMMON RADIUS BUDGET
--
-- On every monotone original source mesh 0<=v_j<=R<1,
-- choose the pinned midpoint rho=(R+1)/2 and let
-- K=inv_B(1-rho)^2. Every source local normalized error obeys:
--
-- |G_N(v_m)-G_N(v_0)| <=
--   sum(j<m) K*|h_j|*[v_j^N+B_N(R,h_j)].
--
-- The forcing estimate and quotient-defect estimate both consume
-- the ACTUAL source bishopExp(-L_N), including the origin cell.
-- This is a finite comparison without selected FTC or synthetic exp.
--
-- The next genuine analytic leaf is a refining original mesh that
-- makes sum h_j*B_N(R,h_j)->0 while the forcing quadrature is
-- bounded by x^(N+1)/(N+1). The finite equality is not P0.06.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ)
import Real as R
import RealProperties as RP
import Sequence as Seq

import DASHI.Analysis.BishopOriginalFiniteNormalizedEndpointComparisonExact as Comp
import DASHI.Analysis.BishopOriginalMeshInverseRadiusExact as InverseRadius
import DASHI.Analysis.BishopOriginalNonnegativeNegativeExpBoundExact as ClosedExp
import DASHI.Analysis.BishopOriginalFiniteLogExpStagewiseUniformDefectExact as Defect
import DASHI.Analysis.BishopOriginalNegativeLogFiniteWeightedMeshRecurrenceExact as Mesh
import DASHI.Analysis.BishopOriginalNormalizedFiniteMeshEndpointExact as Endpoint
import DASHI.Analysis.BishopOriginalFactorIncrementFiniteTelescopeExact as Walk
import DASHI.Analysis.BishopOriginalNegativeLogCrossWeightedIncrementExact as Cross
import DASHI.Analysis.BishopOriginalNegativeLogExpFiniteStageLimitExact as Finite
import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as Gap

sourceMidpointInverseSquare :
  (radius : R.ℝ) →
  Gap.BishopUnitIntervalRatio radius → R.ℝ
sourceMidpointInverseSquare radius radiusRatio =
  let
    inverse = Gap.oneMinusInverse
      (InverseRadius.originalBishopMidpointRadiusRatio
        radius radiusRatio)
  in
  R._*_ inverse inverse

sourceRadiusNormalizedCellBudget :
  (stage : Nat) (radius : R.ℝ) →
  (radiusRatio : Gap.BishopUnitIntervalRatio radius) →
  (steps : Nat → R.ℝ) →
  Nat → R.ℝ
sourceRadiusNormalizedCellBudget stage radius radiusRatio steps j =
  let
    x = Mesh.sourceVertex steps j
    b = Defect.sourceOriginalUniformErrorBudget stage radius (steps j)
  in
  R._*_
    (sourceMidpointInverseSquare radius radiusRatio)
    (R._*_
      (R.∣ steps j ∣)
      (R._+_ (R.pow x stage) b))

originalBishopGapAbsoluteAtMostOne :
  (x : R.ℝ) →
  (ratio : Gap.BishopUnitIntervalRatio x) →
  R._≤_ (R.∣ Cross.oneMinus x ∣) R.1ℝ
originalBishopGapAbsoluteAtMostOne x ratio =
  let
    w = Cross.oneMinus x
    shifted = RP.+-monoʳ-≤
      R.1ℝ
      (RP.neg-mono-≤ (Gap.ratioNonnegative ratio))
    cancellation =
      let open RP.ℝ-Solver in
      solve 0
        (Κ 1ℚᵘ ⊕ (⊝ Κ 0ℚᵘ) ⊜ Κ 1ℚᵘ)
        RP.≃-refl
    bound = RP.≤-respʳ-≃ cancellation shifted
  in
  RP.≤-respˡ-≃
    (RP.nonNegx⇒∣x∣≃x
      (RP.0≤x⇒nonNegx
        (RP.<⇒≤ (Gap.oneMinusPositive ratio))))
    bound

originalBishopWeightTimesExpAbsAtMostOne :
  (stage : Nat) (x : R.ℝ) →
  (ratio : Gap.BishopUnitIntervalRatio x) →
  R._≤_
    (R._*_
      (R.∣ Cross.oneMinus x ∣)
      (R.∣ Finite.originalNegativeLogFiniteExponential x stage ∣))
    R.1ℝ
originalBishopWeightTimesExpAbsAtMostOne stage x ratio =
  let
    w = R.∣ Cross.oneMinus x ∣
    f = R.∣ Finite.originalNegativeLogFiniteExponential x stage ∣
    wBound = originalBishopGapAbsoluteAtMostOne x ratio
    fBound =
      ClosedExp.originalFiniteNegativeLogExpAtMostOneNonnegative
        x (Gap.ratioNonnegativeWitness ratio) stage
  in
  RP.≤-trans
    (RP.≤-respʳ-≃ (RP.*-identityʳ w)
      (RP.*-monoˡ-≤-nonNeg
        fBound (RP.nonNeg∣x∣ (Cross.oneMinus x))))
    wBound

originalBishopNormalizedSourceCellBelowRadiusBudget :
  (stage : Nat) (radius : R.ℝ) →
  (radiusRatio : Gap.BishopUnitIntervalRatio radius) →
  (steps : Nat → R.ℝ) →
  (receipts : (j : Nat) →
    Gap.BishopUnitIntervalRatio (Mesh.sourceVertex steps j)) →
  (inside : (j : Nat) →
    R._≤_ (Mesh.sourceVertex steps j) radius) →
  (j : Nat) →
  R._≤_
    (Comp.sourceNormalizedCellComparisonBudget
      stage radius steps receipts j)
    (sourceRadiusNormalizedCellBudget
      stage radius radiusRatio steps j)
originalBishopNormalizedSourceCellBelowRadiusBudget
    stage radius radiusRatio steps receipts inside j =
  let
    x = Mesh.sourceVertex steps j
    h = steps j
    pair = R._*_
      (Gap.oneMinusInverse (receipts j))
      (Gap.oneMinusInverse (receipts (suc j)))
    common = sourceMidpointInverseSquare radius radiusRatio
    w = R.∣ Cross.oneMinus x ∣
    f = R.∣ Finite.originalNegativeLogFiniteExponential x stage ∣
    power = R.pow x stage
    force = R.∣ Cross.sourceODEForcing stage x ∣
    b = Defect.sourceOriginalUniformErrorBudget stage radius h
    xNN = Gap.ratioNonnegativeWitness (receipts j)
    wFBelowOne = originalBishopWeightTimesExpAbsAtMostOne
      stage x (receipts j)
    radiusNN = Gap.ratioNonnegativeWitness radiusRatio
    bNN = Defect.sourceOriginalUniformErrorBudgetNonnegative
      stage radius h radiusNN
    wFbound =
      RP.≤-respˡ-≃
        (let open RP.ℝ-Solver in
         solve 3
           (λ ww ff bb →
             ww ⊗ (ff ⊗ bb) ⊜ (ww ⊗ ff) ⊗ bb)
           RP.≃-refl w f b)
        (RP.≤-respʳ-≃
          (RP.*-identityˡ b)
          (RP.*-monoʳ-≤-nonNeg wFBelowOne bNN))
    sumBound = RP.+-mono-≤
      (ClosedExp.originalFiniteNegativeLogExpUniformForcingAllNonnegative
        stage radius x xNN (inside j))
      wFbound
    coeffNN = RP.nonNegx,y⇒nonNegx*y
      (RP.nonNeg∣x∣ h)
      (RP.nonNegx,y⇒nonNegx+y
        (Seq.nonNegx⇒nonNegxⁿ stage xNN) bNN)
    normalizedTermBound =
      RP.*-monoˡ-≤-nonNeg
        (RP.*-monoˡ-≤-nonNeg
          sumBound (RP.nonNeg∣x∣ h))
        (RP.nonNegx,y⇒nonNegx*y
          (Gap.oneMinusInverseNonnegative (receipts j))
          (Gap.oneMinusInverseNonnegative (receipts (suc j))))
    pairBound = InverseRadius.originalBishopMeshPairInverseDominatedByRadiusSquare
      steps j radius receipts radiusRatio inside
  in
  RP.≤-trans
    normalizedTermBound
    (RP.*-monoʳ-≤-nonNeg pairBound coeffNN)

originalBishopFiniteNormalizedRadiusEndpointComparison :
  (stage : Nat) (radius : R.ℝ) →
  (radiusRatio : Gap.BishopUnitIntervalRatio radius) →
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
      (sourceRadiusNormalizedCellBudget
        stage radius radiusRatio steps)
      cells)
originalBishopFiniteNormalizedRadiusEndpointComparison
    stage radius radiusRatio steps receipts inside cells =
  RP.≤-trans
    (Comp.originalBishopFiniteNormalizedEndpointResidualComparison
      stage radius steps receipts inside cells)
    (Comp.originalBishopFiniteSumPointwiseMonotone
      (Comp.sourceNormalizedCellComparisonBudget
        stage radius steps receipts)
      (sourceRadiusNormalizedCellBudget
        stage radius radiusRatio steps)
      (originalBishopNormalizedSourceCellBelowRadiusBudget
        stage radius radiusRatio steps receipts inside)
      cells)
