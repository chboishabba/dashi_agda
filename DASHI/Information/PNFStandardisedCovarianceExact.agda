module DASHI.Information.PNFStandardisedCovarianceExact where

-- The same finite covariance operator, with explicit scale and diagonal
-- normalization receipts. Applies to finance *or* PNF activation coordinates.
-- Neither source data nor statistical MP hypotheses are inferred.
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Fin.Base using (Fin)
open import Relation.Binary.PropositionalEquality using (trans; cong)

import DASHI.Physics.Closure.NSTriadKNExactOrderedScalar as Scalar
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffInnerProduct as Ring
import DASHI.Information.PNFFiniteCovarianceEconomicsExact as Matrix
import DASHI.Information.PNFCentredCovarianceExact as Centre

record StandardisedWindow
  (K : Ring.ExactOrderedCommutativeRing)
  (n p : Nat) : Set₁ where
  private
    S = Ring.orderedScalar K
  field
    dataWindow : Centre.FiniteCentredData K n p
    scale : Scalar.Scalar S
    -- Nonconstant columns and a positive denominator are required to
    -- construct this identity from actual source data.
    unitDiagonalSource :
      (i : Fin p) →
      Scalar._*_ S scale
        (Matrix.gram K
          (Centre.centredMatrix K dataWindow) i i)
      ≡ Scalar.one S

open StandardisedWindow public

correlationDiagonalOne :
  (K : Ring.ExactOrderedCommutativeRing) →
  {n p : Nat} →
  (W : StandardisedWindow K n p) →
  (i : Fin p) →
  Centre.scaledCovariance K
    (dataWindow W) (scale W) i i
  ≡ Scalar.one (Ring.orderedScalar K)
correlationDiagonalOne K W i =
  unitDiagonalSource W i

correlationTraceEqualsDimension :
  (K : Ring.ExactOrderedCommutativeRing) →
  {n p : Nat} →
  (W : StandardisedWindow K n p) →
  Ring.sumFin (Ring.orderedScalar K)
    (λ i → Centre.scaledCovariance K
      (dataWindow W) (scale W) i i)
  ≡ Matrix.dimensionScalar K p
correlationTraceEqualsDimension K W =
  trans
    (Ring.sumFinCong (Ring.orderedScalar K)
      (correlationDiagonalOne K W))
    (Matrix.sumConstantOne K)
