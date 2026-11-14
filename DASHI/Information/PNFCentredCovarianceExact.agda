module DASHI.Information.PNFCentredCovarianceExact where

-- A single finite, sourced matrix yields its centred covariance and the
-- associated scaled Gram quadratic. This is algebra, not an iid-null claim.
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Fin.Base using (Fin)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Physics.Closure.NSTriadKNExactOrderedScalar as Scalar
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffInnerProduct as Ring
import DASHI.Information.PNFFiniteCovarianceEconomicsExact as Matrix
import DASHI.Information.PNFFiniteGramPositiveExact as PSD
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffOrbitGramAssembly as ExistingPSD

record FiniteCentredData
    (K : Ring.ExactOrderedCommutativeRing)
    (n p : Nat) : Set where
  private
    S = Ring.orderedScalar K
  field
    raw : Matrix.FiniteMatrix K n p
    columnMean : Fin p → Scalar.Scalar S

open FiniteCentredData public

centredMatrix :
  (K : Ring.ExactOrderedCommutativeRing) →
  {n p : Nat} → FiniteCentredData K n p →
  Matrix.FiniteMatrix K n p
centredMatrix K X = record
  { entry = λ r i →
      Scalar._+_ (Ring.orderedScalar K)
        (Matrix.entry (raw X) r i)
        (Scalar.neg (Ring.orderedScalar K) (columnMean X i))
  }

-- 'scale' is explicitly supplied by the numerical field backend.
-- For the unbiased sample covariance it must equal 1/(n−1) with n>1.
scaledCovariance :
  (K : Ring.ExactOrderedCommutativeRing) →
  {n p : Nat} → (X : FiniteCentredData K n p) →
  Scalar.Scalar (Ring.orderedScalar K) →
  Fin p → Fin p → Scalar.Scalar (Ring.orderedScalar K)
scaledCovariance K X scale i j =
  Scalar._*_ (Ring.orderedScalar K) scale
    (Matrix.gram K (centredMatrix K X) i j)

scaledCovarianceSymmetric :
  (K : Ring.ExactOrderedCommutativeRing) →
  {n p : Nat} → (X : FiniteCentredData K n p) →
  (scale : Scalar.Scalar (Ring.orderedScalar K)) →
  (i j : Fin p) →
  scaledCovariance K X scale i j ≡
  scaledCovariance K X scale j i
scaledCovarianceSymmetric K X scale i j =
  cong (Scalar._*_ (Ring.orderedScalar K) scale)
    (Matrix.sampleGramSymmetric K (centredMatrix K X) i j)

scaledGramQuadratic :
  (K : Ring.ExactOrderedCommutativeRing) →
  {n p : Nat} → (X : FiniteCentredData K n p) →
  (scale : Scalar.Scalar (Ring.orderedScalar K)) →
  (Fin p → Scalar.Scalar (Ring.orderedScalar K)) →
  Scalar.Scalar (Ring.orderedScalar K)
scaledGramQuadratic K X scale v =
  Scalar._*_ (Ring.orderedScalar K) scale
    (PSD.gramQuadratic K (centredMatrix K X) v)

scaledGramQuadraticNonnegative :
  (K : Ring.ExactOrderedCommutativeRing) →
  (P : PSD.PositiveCone K) →
  {n p : Nat} → (X : FiniteCentredData K n p) →
  (scale : Scalar.Scalar (Ring.orderedScalar K)) →
  Scalar._≤_ (Ring.orderedScalar K)
    (Scalar.zero (Ring.orderedScalar K)) scale →
  (v : Fin p → Scalar.Scalar (Ring.orderedScalar K)) →
  Scalar._≤_ (Ring.orderedScalar K)
    (Scalar.zero (Ring.orderedScalar K))
    (scaledGramQuadratic K X scale v)
scaledGramQuadraticNonnegative K P X scale scaleNonnegative v =
  Scalar.multiplicationPreservesNonnegative (Ring.orderedScalar K)
    scaleNonnegative
    (PSD.finiteMatrixGramPositiveSemidefinite K P (centredMatrix K X) v)

-- Existing DASHI PSD authority is the owner; this lemma transfers its
-- finite Gram positivity to the centred *same matrix* and nonnegative scale.
centredCovarianceGramPSDFromExisting :
  (K : Ring.ExactOrderedCommutativeRing) →
  (O : ExistingPSD.FiniteGramOrderAuthority K) →
  {n p : Nat} → (X : FiniteCentredData K n p) →
  (scale : Scalar.Scalar (Ring.orderedScalar K)) →
  Scalar._≤_ (Ring.orderedScalar K)
    (Scalar.zero (Ring.orderedScalar K)) scale →
  (v : Fin p → Scalar.Scalar (Ring.orderedScalar K)) →
  Scalar._≤_ (Ring.orderedScalar K)
    (Scalar.zero (Ring.orderedScalar K))
    (scaledGramQuadratic K X scale v)
centredCovarianceGramPSDFromExisting K O X scale scaleNonnegative v =
  scaledGramQuadraticNonnegative
    K (PSD.positiveConeFromExistingPSD K O)
    X scale scaleNonnegative v
