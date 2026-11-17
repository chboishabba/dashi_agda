module DASHI.Analysis.BishopOriginalFiniteErrorQuadratureRemainderBoundExact where

------------------------------------------------------------------------
-- K04d P0.06: LITERAL ORIGINAL FINITE LOG ERROR ENDPOINT BOUND.
--
-- This is no longer a normalized selected-function proxy.
-- For any genuine monotone original Bishop mesh 0<=v_j<=R<1:
--
-- |F_N(v_m)-(1-v_m)| <= K(R) *
--   [ (v_m^(N+1)-v_0^(N+1))/(N+1)
--      + SUM(j<m) h_j*B_N(R,h_j) ],
--
-- K(R)=inv_B(1-(R+1)/2)^2, B_N is the ACTUAL original error
-- quotient modulus. The source proof consumes the original
-- finite LOG error identity including the initial value F_N(0)=1.
--
-- This is a finite certified comparison *in source code*,
-- subject to Agda kernel acceptance; to discharge P0.06 exactly
-- still requires a mesh refining to the SAME endpoint v_m=x and
-- with the remainder tending to zero.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
import Real as R
import RealProperties as RP

import DASHI.Analysis.BishopOriginalNormalizedFiniteEndpointErrorWeldExact as Weld
import DASHI.Analysis.BishopOriginalFiniteNormalizedEndpointQuadratureRemainderExact as Quad
import DASHI.Analysis.BishopOriginalFiniteNormalizedRadiusBudgetExact as Radius
import DASHI.Analysis.BishopOriginalNegativeLogFiniteWeightedMeshRecurrenceExact as Mesh
import DASHI.Analysis.BishopOriginalNormalizedFiniteMeshEndpointExact as Endpoint
import DASHI.Analysis.BishopOriginalNegativeLogFiniteErrorDerivativeExact as Error
import DASHI.Analysis.BishopOriginalNegativeLogCrossWeightedIncrementExact as Cross
import DASHI.Analysis.BishopOriginalFiniteLogExpStagewiseUniformDefectExact as Defect
import DASHI.Analysis.BishopOriginalFactorIncrementFiniteTelescopeExact as Walk
import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as Gap
import DASHI.Foundations.BishopNatRealReciprocalSquareBaselExact as Recip

originalSourceFiniteErrorMeshIsNormalizedEndpoint :
  (stage : Nat) (steps : Nat → R.ℝ) →
  (receipts : (j : Nat) →
    Gap.BishopUnitIntervalRatio (Mesh.sourceVertex steps j)) →
  (cells : Nat) →
  let
    x = Mesh.sourceVertex steps cells
  in
  R._≃_
    (Error.originalFiniteLogExpError stage x)
    (R._*_
      (Cross.oneMinus x)
      (R._-_
        (Endpoint.sourceNormalizedMeshAt
          stage steps receipts cells)
        (Endpoint.sourceNormalizedMeshAt
          stage steps receipts zero)))
originalSourceFiniteErrorMeshIsNormalizedEndpoint
    stage steps receipts cells =
  Weld.originalFiniteNormalizedEndpointErrorWithAnyOriginRatio
    stage
    (Mesh.sourceVertex steps cells)
    (receipts cells)
    (receipts zero)

originalFiniteErrorMeshAbsoluteBelowNormalizedIncrement :
  (stage : Nat) (steps : Nat → R.ℝ) →
  (receipts : (j : Nat) →
    Gap.BishopUnitIntervalRatio (Mesh.sourceVertex steps j)) →
  (cells : Nat) →
  R._≤_
    (R.∣ Error.originalFiniteLogExpError
      stage (Mesh.sourceVertex steps cells) ∣)
    (R.∣ R._-_
      (Endpoint.sourceNormalizedMeshAt
        stage steps receipts cells)
      (Endpoint.sourceNormalizedMeshAt
        stage steps receipts zero) ∣)
originalFiniteErrorMeshAbsoluteBelowNormalizedIncrement
    stage steps receipts cells =
  let
    x = Mesh.sourceVertex steps cells
    w = Cross.oneMinus x
    diff = R._-_
      (Endpoint.sourceNormalizedMeshAt
        stage steps receipts cells)
      (Endpoint.sourceNormalizedMeshAt
        stage steps receipts zero)
    originalErrorEq =
      originalSourceFiniteErrorMeshIsNormalizedEndpoint
        stage steps receipts cells
    absEq = RP.≃-trans
      (RP.∣-∣-cong originalErrorEq)
      (RP.∣x*y∣≃∣x∣*∣y∣ w diff)
    upper =
      RP.≤-respʳ-≃
        (RP.*-identityˡ (R.∣ diff ∣))
        (RP.*-monoʳ-≤-nonNeg
          (Radius.originalBishopGapAbsoluteAtMostOne
            x (receipts cells))
          (RP.nonNeg∣x∣ diff))
  in
  RP.≤-respˡ-≃ absEq upper

originalFiniteNegativeLogExpUniformEndpointRemainderBound :
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
    x = Mesh.sourceVertex steps cells
    endpoint = R._-_
      (R.pow x (suc stage))
      (R.pow (Mesh.sourceVertex steps zero) (suc stage))
    reciprocal = R._⋆ (Recip.reciprocalNatRational stage)
    remainder = Walk.sumFinite
      (Quad.sourceDefectQuadratureCell stage radius steps) cells
  in
  R._≤_
    (R.∣ Error.originalFiniteLogExpError stage x ∣)
    (R._*_
      (Radius.sourceMidpointInverseSquare radius radiusRatio)
      (R._+_
        (R._*_ reciprocal endpoint)
        remainder))
originalFiniteNegativeLogExpUniformEndpointRemainderBound
    stage radius radiusRatio steps receipts inside stepNN cells =
  RP.≤-trans
    (originalFiniteErrorMeshAbsoluteBelowNormalizedIncrement
      stage steps receipts cells)
    (Quad.originalFiniteNormalizedEndpointQuadratureRemainderBound
      stage radius radiusRatio steps receipts inside stepNN cells)
