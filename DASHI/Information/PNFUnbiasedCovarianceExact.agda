module DASHI.Information.PNFUnbiasedCovarianceExact where

-- Reusable finite sample covariance certification.
-- The field/inverse and source identification are explicit receipts:
-- this module never infers an actual market/PNF observation source.
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Fin.Base using (Fin)

import DASHI.Physics.Closure.NSTriadKNExactOrderedScalar as Scalar
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffInnerProduct as Ring
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffOrbitGramAssembly as ExistingPSD
import DASHI.Information.PNFFiniteCovarianceEconomicsExact as Matrix
import DASHI.Information.PNFCentredCovarianceExact as Centre
import DASHI.Information.PNFSampleMeanExact as Mean
import DASHI.Information.PNFCovarianceQuadraticIdentityExact as Quadratic

record UnbiasedCovarianceWindow
  (K : Ring.ExactOrderedCommutativeRing)
  (k p : Nat) : Set₁ where
  private
    S = Ring.orderedScalar K
  field
    -- Sample count is suc(suc k), so n-1 = suc k is strictly positive.
    actualMeans : Mean.ActualFiniteMean K (suc (suc k)) p
    scale : Scalar.Scalar S
    scaleIsInverseSampleMinusOne :
      Scalar._*_ S scale (Matrix.dimensionScalar K (suc k))
      ≡ Scalar.one S
    positiveScale :
      Scalar._≤_ S (Scalar.zero S) scale

open UnbiasedCovarianceWindow public

unbiasedCenteredColumnSumZero :
  (K : Ring.ExactOrderedCommutativeRing) →
  {k p : Nat} →
  (W : UnbiasedCovarianceWindow K k p) →
  (i : Fin p) →
  Ring.sumFin (Ring.orderedScalar K)
    (λ r → Matrix.entry
      (Centre.centredMatrix K (Mean.source (actualMeans W))) r i)
  ≡ Scalar.zero (Ring.orderedScalar K)
unbiasedCenteredColumnSumZero K W =
  Mean.sampleMeanDefiningEquation K (actualMeans W)

unbiasedCovarianceOperatorPSD :
  (K : Ring.ExactOrderedCommutativeRing) →
  (O : ExistingPSD.FiniteGramOrderAuthority K) →
  {k p : Nat} →
  (W : UnbiasedCovarianceWindow K k p) →
  (v : Fin p → Scalar.Scalar (Ring.orderedScalar K)) →
  Scalar._≤_ (Ring.orderedScalar K)
    (Scalar.zero (Ring.orderedScalar K))
    (Quadratic.covarianceOperatorQuadratic K
      (Mean.source (actualMeans W)) (scale W) v)
unbiasedCovarianceOperatorPSD K O W =
  Quadratic.covarianceOperatorPositiveSemidefinite K O
    (Mean.source (actualMeans W)) (scale W) (positiveScale W)

unbiasedCovarianceSymmetric :
  (K : Ring.ExactOrderedCommutativeRing) →
  {k p : Nat} →
  (W : UnbiasedCovarianceWindow K k p) →
  (i j : Fin p) →
  Centre.scaledCovariance K
    (Mean.source (actualMeans W)) (scale W) i j
  ≡
  Centre.scaledCovariance K
    (Mean.source (actualMeans W)) (scale W) j i
unbiasedCovarianceSymmetric K W =
  Centre.scaledCovarianceSymmetric K
    (Mean.source (actualMeans W)) (scale W)
