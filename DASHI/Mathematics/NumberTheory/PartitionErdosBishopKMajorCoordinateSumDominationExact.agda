module DASHI.Mathematics.NumberTheory.PartitionErdosBishopKMajorCoordinateSumDominationExact where

------------------------------------------------------------------------
-- LIFT POINTWISE K-MAJOR DOMINATION TO THE CERTIFIED FINITE CARRIER
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Nat.Base using (_≤_)

import Real as BishopReal

import DASHI.Foundations.BishopFinitePermutationFoldExact as Fold
import DASHI.Mathematics.NumberTheory.PartitionErdosBishopCubicStepRateExact as Rate
import DASHI.Mathematics.NumberTheory.PartitionErdosBishopKMajorCoordinateDominationExact as Pointwise
import DASHI.Mathematics.NumberTheory.PartitionErdosKMajorFactorCoordinateExact as KMajor
open import DASHI.Physics.YangMills.CompactLieProofLevel

kMajorCoordinateResidualSum : Nat → BishopReal.ℝ
kMajorCoordinateResidualSum n =
  Fold.bishopFold
    (Pointwise.coordinateResidualWeight n)
    (KMajor.kMajorFactorCoordinates n)

kMajorCoordinateCubicSum :
  ∀ {n} {nPositive : suc 0 ≤ n} →
  Rate.ErdosStepRate n nPositive → BishopReal.ℝ
kMajorCoordinateCubicSum {n} rate =
  Fold.bishopFold
    (Pointwise.coordinateCubicWeight rate)
    (KMajor.kMajorFactorCoordinates n)

kMajorCoordinateResidualBelowCubic :
  ∀ {n : Nat} →
  (nPositive : suc 0 ≤ n) →
  let rate = Rate.canonicalErdosStepRate n nPositive in
  BishopReal._≤_
    (kMajorCoordinateResidualSum n)
    (kMajorCoordinateCubicSum rate)
kMajorCoordinateResidualBelowCubic {n} nPositive =
  Fold.bishopFoldPointwise
    (Pointwise.coordinateResidualWeight n)
    (Pointwise.coordinateCubicWeight
      (Rate.canonicalErdosStepRate n nPositive))
    (KMajor.kMajorFactorCoordinates n)
    (Pointwise.coordinateResidualBelowCubic nPositive)

partitionErdosBishopKMajorCoordinateSumDominationLevel : ProofLevel
partitionErdosBishopKMajorCoordinateSumDominationLevel = machineChecked
