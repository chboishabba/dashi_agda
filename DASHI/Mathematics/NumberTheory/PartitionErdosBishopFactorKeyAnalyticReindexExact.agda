module DASHI.Mathematics.NumberTheory.PartitionErdosBishopFactorKeyAnalyticReindexExact where

------------------------------------------------------------------------
-- BISHOP ANALYTIC WEIGHT ON THE EXACT FACTOR-KEY REINDEX
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopCubicTranslationIteratedExact as Iterated
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopFinitePermutationFoldExact as Fold
import DASHI.Mathematics.NumberTheory.PartitionErdosBishopCubicStepRateExact as Rate
import DASHI.Mathematics.NumberTheory.PartitionErdosBishopKMajorCoordinateDominationExact as Coordinate
import DASHI.Mathematics.NumberTheory.PartitionErdosFactorCoordinateKeyExact as Key
import DASHI.Mathematics.NumberTheory.PartitionErdosFactorKeyPermutationExact as Permutation
import DASHI.Mathematics.NumberTheory.PartitionErdosKMajorFactorCoordinateExact as KMajor
import DASHI.Mathematics.NumberTheory.PartitionErdosResidualMajorFactorKeyExact as ResidualMajor
open import DASHI.Physics.YangMills.CompactLieProofLevel

factorAnalyticWeight : Nat → Key.FactorCoordinateKey → BishopReal.ℝ
factorAnalyticWeight n key =
  BishopReal._*_
    (Iterated.natReal (Key.divisor key))
    (Exp.bishopExp
      (Rate.residualExponent n (Key.residual key)))

residualMajorAnalyticFactorSum : Nat → BishopReal.ℝ
residualMajorAnalyticFactorSum n =
  Fold.bishopFold
    (factorAnalyticWeight n)
    (ResidualMajor.residualMajorFactorKeys n)

kMajorAnalyticFactorSum : Nat → BishopReal.ℝ
kMajorAnalyticFactorSum n =
  Fold.bishopFold
    (factorAnalyticWeight n)
    (Permutation.kMajorFactorKeys n)

residualMajorEqualsKMajorAnalyticFactorSum :
  ∀ n →
  BishopReal._≃_
    (residualMajorAnalyticFactorSum n)
    (kMajorAnalyticFactorSum n)
residualMajorEqualsKMajorAnalyticFactorSum n =
  Fold.bishopFoldPermutationInvariant
    (factorAnalyticWeight n)
    (Permutation.residualMajorKMajorFactorKeyPermutation n)

kMajorEqualsResidualMajorAnalyticFactorSum :
  ∀ n →
  BishopReal._≃_
    (kMajorAnalyticFactorSum n)
    (residualMajorAnalyticFactorSum n)
kMajorEqualsResidualMajorAnalyticFactorSum n =
  Fold.bishopFoldPermutationInvariant
    (factorAnalyticWeight n)
    (Permutation.kMajorResidualMajorFactorKeyPermutation n)

kMajorKeySumIsCoordinateResidualSum :
  ∀ n →
  BishopReal._≃_
    (kMajorAnalyticFactorSum n)
    (Fold.bishopFold
      (Coordinate.coordinateResidualWeight n)
      (KMajor.kMajorFactorCoordinates n))
kMajorKeySumIsCoordinateResidualSum n =
  Fold.bishopFoldMap
    (factorAnalyticWeight n)
    Key.kMajorFactorKey
    (KMajor.kMajorFactorCoordinates n)

residualMajorIsCoordinateResidualSum :
  ∀ n →
  BishopReal._≃_
    (residualMajorAnalyticFactorSum n)
    (Fold.bishopFold
      (Coordinate.coordinateResidualWeight n)
      (KMajor.kMajorFactorCoordinates n))
residualMajorIsCoordinateResidualSum n =
  BishopP.≃-trans
    (residualMajorEqualsKMajorAnalyticFactorSum n)
    (kMajorKeySumIsCoordinateResidualSum n)

partitionErdosBishopFactorKeyAnalyticReindexLevel : ProofLevel
partitionErdosBishopFactorKeyAnalyticReindexLevel = machineChecked
