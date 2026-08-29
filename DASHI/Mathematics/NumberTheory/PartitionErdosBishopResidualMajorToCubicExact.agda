module DASHI.Mathematics.NumberTheory.PartitionErdosBishopResidualMajorToCubicExact where

------------------------------------------------------------------------
-- RESIDUAL-MAJOR FACTOR SUM <= K-MAJOR CUBIC SUM
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Nat.Base using (_≤_)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Mathematics.NumberTheory.PartitionErdosBishopFactorKeyAnalyticReindexExact as Reindex
import DASHI.Mathematics.NumberTheory.PartitionErdosBishopKMajorCoordinateSumDominationExact as KSum
open import DASHI.Physics.YangMills.CompactLieProofLevel

residualMajorAnalyticFactorSumBelowCubic :
  ∀ {n : Nat} →
  (nPositive : suc 0 ≤ n) →
  BishopReal._≤_
    (Reindex.residualMajorAnalyticFactorSum n)
    (KSum.kMajorCoordinateCubicSum
      (DASHI.Mathematics.NumberTheory.PartitionErdosBishopCubicStepRateExact.canonicalErdosStepRate
        n nPositive))
residualMajorAnalyticFactorSumBelowCubic {n} nPositive =
  BishopP.≤-respˡ-≃
    (Reindex.residualMajorIsCoordinateResidualSum n)
    (KSum.kMajorCoordinateResidualBelowCubic nPositive)

partitionErdosBishopResidualMajorToCubicLevel : ProofLevel
partitionErdosBishopResidualMajorToCubicLevel = machineChecked
