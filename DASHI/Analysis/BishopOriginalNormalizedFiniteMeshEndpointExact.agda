module DASHI.Analysis.BishopOriginalNormalizedFiniteMeshEndpointExact where

------------------------------------------------------------------------
-- K04d P0.05: ALL-CELL NORMALIZED ORIGINAL BISHOP ENDPOINT.
--
-- Reuse the P0.04 original positive gap/reciprocal witnesses and
-- P0.05 normalized TWO-point local residual identity.
--
-- For genuine original finiteWalk vertices v_j and supplied
-- source unit-interval receipts, put G_N(v)=F_N(v)/(1-v).
-- Then for EVERY finite cell count m, exactly:
--
-- G_N(v_m)-G_N(v_0) =
--   sum_{j<m} inv(w_j)*inv(w_(j+1))*h_j*
--     [v_j^N F_N(v_j)+w_j*(q_E(j)-E'_N(v_j))].
--
-- No MVT/FTC, no product-weight division, no derivative slope
-- substituted for a positive increment, no new exponential.
--
-- This settles the FINITE normalized telescope algebra; P0.05's
-- order/comparison and the P0.06 analytic limit remain unpaid.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ)
import Real as R
import RealProperties as RP

import DASHI.Analysis.BishopOriginalFactorIncrementFiniteTelescopeExact as Walk
import DASHI.Analysis.BishopOriginalNegativeLogFiniteWeightedMeshRecurrenceExact as Mesh
import DASHI.Analysis.BishopOriginalNormalizedExpIncrementExact as Normalized
import DASHI.Analysis.BishopOriginalNegativeLogCrossWeightedIncrementExact as Cross
import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as Gap

sourceNormalizedMeshAt :
  (stage : Nat) →
  (steps : Nat → R.ℝ) →
  ((j : Nat) → Gap.BishopUnitIntervalRatio (Mesh.sourceVertex steps j)) →
  Nat → R.ℝ
sourceNormalizedMeshAt stage steps receipts j =
  Normalized.originalNormalizedFiniteExp
    stage (Mesh.sourceVertex steps j) (receipts j)

sourceNormalizedMeshIncrement :
  (stage : Nat) →
  (steps : Nat → R.ℝ) →
  (receipts : (j : Nat) →
    Gap.BishopUnitIntervalRatio (Mesh.sourceVertex steps j)) →
  Nat → R.ℝ
sourceNormalizedMeshIncrement stage steps receipts j =
  R._-_
    (sourceNormalizedMeshAt stage steps receipts (suc j))
    (sourceNormalizedMeshAt stage steps receipts j)

sourceNormalizedMeshResidualCell :
  (stage : Nat) →
  (steps : Nat → R.ℝ) →
  (receipts : (j : Nat) →
    Gap.BishopUnitIntervalRatio (Mesh.sourceVertex steps j)) →
  Nat → R.ℝ
sourceNormalizedMeshResidualCell stage steps receipts j =
  let
    x = Mesh.sourceVertex steps j
    waInverse = Gap.oneMinusInverse (receipts j)
    wbInverse = Gap.oneMinusInverse (receipts (suc j))
    residual =
      R._+_
        (Cross.sourceODEForcing stage x)
        (R._*_ (Cross.oneMinus x)
          (R._-_
            (Cross.sourceErrorQuotient stage x (steps j))
            (Cross.sourceErrorSlope stage x)))
  in
  R._*_
    (R._*_ waInverse wbInverse)
    (R._*_ (steps j) residual)

originalNormalizedMeshIncrementIsResidualCell :
  (stage : Nat) (steps : Nat → R.ℝ) →
  (receipts : (j : Nat) →
    Gap.BishopUnitIntervalRatio (Mesh.sourceVertex steps j)) →
  (j : Nat) →
  R._≃_
    (sourceNormalizedMeshIncrement stage steps receipts j)
    (sourceNormalizedMeshResidualCell stage steps receipts j)
originalNormalizedMeshIncrementIsResidualCell
    stage steps receipts j =
  Normalized.originalNormalizedFiniteExpUnweightedIncrement
    stage (Mesh.sourceVertex steps j) (steps j)
    (receipts j) (receipts (suc j))

-- Finite source function sequence telescope on the same original
-- R.ℝ carrier. This avoids building an independently selected FTC.
sourceFiniteSequenceIncrementTelescope :
  (f : Nat → R.ℝ) (n : Nat) →
  R._≃_
    (Walk.sumFinite
      (λ j → R._-_ (f (suc j)) (f j))
      n)
    (R._-_ (f n) (f zero))
sourceFiniteSequenceIncrementTelescope f zero =
  let open RP.ℝ-Solver in
  solve 1
    (λ first → Κ 0ℚᵘ ⊜ first ⊖ first)
    RP.≃-refl (f zero)
sourceFiniteSequenceIncrementTelescope f (suc n) =
  RP.≃-trans
    (RP.+-cong
      (sourceFiniteSequenceIncrementTelescope f n)
      RP.≃-refl)
    (let open RP.ℝ-Solver in
     solve 3
       (λ old first next →
         (old ⊖ first) ⊕ (next ⊖ old)
         ⊜ next ⊖ first)
       RP.≃-refl (f n) (f zero) (f (suc n)))

originalNormalizedMeshResidualSumIsIncrementSum :
  (stage : Nat) (steps : Nat → R.ℝ) →
  (receipts : (j : Nat) →
    Gap.BishopUnitIntervalRatio (Mesh.sourceVertex steps j)) →
  (n : Nat) →
  R._≃_
    (Walk.sumFinite
      (sourceNormalizedMeshIncrement stage steps receipts) n)
    (Walk.sumFinite
      (sourceNormalizedMeshResidualCell stage steps receipts) n)
originalNormalizedMeshResidualSumIsIncrementSum
    stage steps receipts zero = RP.≃-refl
originalNormalizedMeshResidualSumIsIncrementSum
    stage steps receipts (suc n) =
  RP.+-cong
    (originalNormalizedMeshResidualSumIsIncrementSum
      stage steps receipts n)
    (originalNormalizedMeshIncrementIsResidualCell
      stage steps receipts n)

originalNormalizedFiniteMeshEndpointIsSourceResidualBudget :
  (stage : Nat) (steps : Nat → R.ℝ) →
  (receipts : (j : Nat) →
    Gap.BishopUnitIntervalRatio (Mesh.sourceVertex steps j)) →
  (cells : Nat) →
  R._≃_
    (R._-_
      (sourceNormalizedMeshAt stage steps receipts cells)
      (sourceNormalizedMeshAt stage steps receipts zero))
    (Walk.sumFinite
      (sourceNormalizedMeshResidualCell stage steps receipts) cells)
originalNormalizedFiniteMeshEndpointIsSourceResidualBudget
    stage steps receipts cells =
  RP.≃-trans
    (RP.≃-symm
      (sourceFiniteSequenceIncrementTelescope
        (sourceNormalizedMeshAt stage steps receipts) cells))
    (originalNormalizedMeshResidualSumIsIncrementSum
      stage steps receipts cells)
