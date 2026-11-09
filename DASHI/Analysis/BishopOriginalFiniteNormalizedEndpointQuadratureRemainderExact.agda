module DASHI.Analysis.BishopOriginalFiniteNormalizedEndpointQuadratureRemainderExact where

------------------------------------------------------------------------
-- K04d P0.06 PRECURSOR: ORIGINAL FINITE ENDPOINT ERROR COMPARISON.
--
-- For actual source nonnegative steps h_j, unit-interval vertices
-- 0<=v_j<=R<1 and the selected N, put rho=(1+R)/2 and
-- K=inv_B(1-rho)^2. The original normalized endpoint satisfies:
--
-- |G_N(v_m)-G_N(v_0)| <= K *
--   [ (v_m^(N+1)-v_0^(N+1))/(N+1)
--       + SUM(j<m) h_j B_N(R,h_j) ].
--
-- All denominators are actual Bishop Nat and gap inverses.
-- The first term comes from the source finite-power polynomial
-- quotient; the second is the actual source finite-log
-- exponential quotient defect modulus. There is no synthetic
-- integral, MVT, FTC, or alternate LOG.
--
-- A uniform refining finite mesh with SUM h_j B_N(R,h_j)->0
-- is still required to obtain the endpoint P0.06 inequality.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
import Real as R
import RealProperties as RP

import DASHI.Analysis.BishopOriginalFiniteNormalizedRadiusBudgetExact as Radius
import DASHI.Analysis.BishopOriginalFinitePowerQuadratureExact as Power
import DASHI.Analysis.BishopOriginalNormalizedFiniteMeshEndpointExact as Endpoint
import DASHI.Analysis.BishopOriginalFiniteLogExpStagewiseUniformDefectExact as Defect
import DASHI.Analysis.BishopOriginalNegativeLogFiniteWeightedMeshRecurrenceExact as Mesh
import DASHI.Analysis.BishopOriginalFactorIncrementFiniteTelescopeExact as Walk
import DASHI.Analysis.BishopOriginalMeshInverseRadiusExact as InvRadius
import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as Gap
import DASHI.Foundations.BishopNatRealReciprocalSquareBaselExact as Recip

sourceDefectQuadratureCell :
  (stage : Nat) (radius : R.ℝ) →
  (steps : Nat → R.ℝ) → Nat → R.ℝ
sourceDefectQuadratureCell stage radius steps j =
  R._*_
    (steps j)
    (Defect.sourceOriginalUniformErrorBudget
      stage radius (steps j))

sourceQuadratureRemainderBudget :
  (stage : Nat) (radius : R.ℝ) →
  (steps : Nat → R.ℝ) (cells : Nat) → R.ℝ
sourceQuadratureRemainderBudget stage radius steps cells =
  R._+_
    (Walk.sumFinite
      (Power.sourceRawPowerQuadratureCell steps stage) cells)
    (Walk.sumFinite
      (sourceDefectQuadratureCell stage radius steps) cells)

sourceRadiusMeshSumIsScaledQuadratureRemainder :
  (stage : Nat) (radius : R.ℝ) →
  (radiusRatio : Gap.BishopUnitIntervalRatio radius) →
  (steps : Nat → R.ℝ) →
  (stepNN : (j : Nat) → R.NonNegative (steps j)) →
  (cells : Nat) →
  R._≃_
    (Walk.sumFinite
      (Radius.sourceRadiusNormalizedCellBudget
        stage radius radiusRatio steps) cells)
    (R._*_
      (Radius.sourceMidpointInverseSquare radius radiusRatio)
      (sourceQuadratureRemainderBudget stage radius steps cells))
sourceRadiusMeshSumIsScaledQuadratureRemainder
    stage radius radiusRatio steps stepNN zero =
  let
    k = Radius.sourceMidpointInverseSquare radius radiusRatio
    open RP.ℝ-Solver
  in
  solve 1
    (λ kk → Κ 0ℚᵘ ⊜ kk ⊗ (Κ 0ℚᵘ ⊕ Κ 0ℚᵘ))
    RP.≃-refl k
sourceRadiusMeshSumIsScaledQuadratureRemainder
    stage radius radiusRatio steps stepNN (suc cells) =
  let
    k = Radius.sourceMidpointInverseSquare radius radiusRatio
    a = Walk.sumFinite
      (Power.sourceRawPowerQuadratureCell steps stage) cells
    b = Walk.sumFinite
      (sourceDefectQuadratureCell stage radius steps) cells
    h = steps cells
    power = R.pow (Mesh.sourceVertex steps cells) stage
    defect = Defect.sourceOriginalUniformErrorBudget stage radius h
    localNormalized =
      RP.*-cong RP.≃-refl
        (RP.*-cong
          (RP.nonNegx⇒∣x∣≃x (stepNN cells))
          RP.≃-refl)
    open RP.ℝ-Solver
  in
  RP.≃-trans
    (RP.+-cong
      (sourceRadiusMeshSumIsScaledQuadratureRemainder
        stage radius radiusRatio steps stepNN cells)
      localNormalized)
    (solve 6
      (λ kk aa bb hh pp dd →
        (kk ⊗ (aa ⊕ bb))
          ⊕ (kk ⊗ (hh ⊗ (pp ⊕ dd)))
        ⊜ kk ⊗
          ((aa ⊕ (hh ⊗ pp))
            ⊕ (bb ⊕ (hh ⊗ dd))))
      RP.≃-refl k a b h power defect)

sourceMidpointInverseSquareNonnegative :
  (radius : R.ℝ) →
  (ratio : Gap.BishopUnitIntervalRatio radius) →
  R.NonNegative
    (Radius.sourceMidpointInverseSquare radius ratio)
sourceMidpointInverseSquareNonnegative radius ratio =
  let
    rMid = InvRadius.originalBishopMidpointRadiusRatio radius ratio
  in
  RP.nonNegx,y⇒nonNegx*y
    (Gap.oneMinusInverseNonnegative rMid)
    (Gap.oneMinusInverseNonnegative rMid)

originalFiniteNormalizedEndpointQuadratureRemainderBound :
  (stage : Nat) (radius : R.ℝ) →
  (radiusRatio : Gap.BishopUnitIntervalRatio radius) →
  (steps : Nat → R.ℝ) →
  (receipts : (j : Nat) →
    Gap.BishopUnitIntervalRatio (Mesh.sourceVertex steps j)) →
  (inside : (j : Nat) →
    R._≤_ (Mesh.sourceVertex steps j) radius) →
  (stepNN : (j : Nat) → R.NonNegative (steps j)) →
  (cells : Nat) →
  let
    endpoint = R._-_
      (R.pow (Mesh.sourceVertex steps cells) (suc stage))
      (R.pow (Mesh.sourceVertex steps zero) (suc stage))
    reciprocal = R._⋆ (Recip.reciprocalNatRational stage)
    remainder = Walk.sumFinite
      (sourceDefectQuadratureCell stage radius steps) cells
  in
  R._≤_
    (R.∣ R._-_
      (Endpoint.sourceNormalizedMeshAt
        stage steps receipts cells)
      (Endpoint.sourceNormalizedMeshAt
        stage steps receipts zero) ∣)
    (R._*_
      (Radius.sourceMidpointInverseSquare radius radiusRatio)
      (R._+_
        (R._*_ reciprocal endpoint)
        remainder))
originalFiniteNormalizedEndpointQuadratureRemainderBound
    stage radius radiusRatio steps receipts inside stepNN cells =
  let
    k = Radius.sourceMidpointInverseSquare radius radiusRatio
    a = Walk.sumFinite
      (Power.sourceRawPowerQuadratureCell steps stage) cells
    endpoint = R._-_
      (R.pow (Mesh.sourceVertex steps cells) (suc stage))
      (R.pow (Mesh.sourceVertex steps zero) (suc stage))
    reciprocal = R._⋆ (Recip.reciprocalNatRational stage)
    b = Walk.sumFinite
      (sourceDefectQuadratureCell stage radius steps) cells
    quadratureBound =
      Power.originalFinitePowerQuadratureEndpointReciprocalBound
        steps stage cells
        (λ j → Gap.ratioNonnegativeWitness (receipts j))
        stepNN
    scaledBound =
      RP.*-monoˡ-≤-nonNeg
        (RP.+-mono-≤ quadratureBound RP.≤-refl)
        (sourceMidpointInverseSquareNonnegative radius radiusRatio)
  in
  RP.≤-trans
    (Radius.originalBishopFiniteNormalizedRadiusEndpointComparison
      stage radius radiusRatio steps receipts inside cells)
    (RP.≤-trans
      (RP.≤-respˡ-≃
        (sourceRadiusMeshSumIsScaledQuadratureRemainder
          stage radius radiusRatio steps stepNN cells)
        RP.≤-refl)
      scaledBound)
