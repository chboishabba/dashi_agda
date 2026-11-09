module DASHI.Information.PNFCentredRankDependencyExact where

-- Constructive linear dependency of centred sample rows.
-- This is a genuine n-to-(n-1) dependency witness, not yet a
-- general rank/nullity theorem (which needs a field/vector-space rank).
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Fin.Base using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Physics.Closure.NSTriadKNExactOrderedScalar as Scalar
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffInnerProduct as Ring
import DASHI.Information.PNFFiniteCovarianceEconomicsExact as Matrix
import DASHI.Information.PNFCentredCovarianceExact as Centre
import DASHI.Information.PNFSampleMeanExact as Mean

private
  SOf : Ring.ExactOrderedCommutativeRing → Set
  SOf K = Scalar.Scalar (Ring.orderedScalar K)

addInverseRight :
  (K : Ring.ExactOrderedCommutativeRing) →
  (b : SOf K) →
  Scalar._+_ (Ring.orderedScalar K)
    b (Scalar.neg (Ring.orderedScalar K) b)
  ≡ Scalar.zero (Ring.orderedScalar K)
addInverseRight K b =
  trans
    (Ring.addCommutative K b (Scalar.neg (Ring.orderedScalar K) b))
    (Ring.addInverseLeft K b)

sumToZeroDeterminesFirst :
  (K : Ring.ExactOrderedCommutativeRing) →
  (a b : SOf K) →
  Scalar._+_ (Ring.orderedScalar K) a b
    ≡ Scalar.zero (Ring.orderedScalar K) →
  a ≡ Scalar.neg (Ring.orderedScalar K) b
sumToZeroDeterminesFirst K a b witness =
  let S = Ring.orderedScalar K in
  trans
    (sym (Ring.addZeroRight K a))
    (trans
      (cong (Scalar._+_ S a)
        (sym (addInverseRight K b)))
      (trans
        (sym (Ring.addAssociative K a b (Scalar.neg S b)))
        (trans
          (cong (λ q → Scalar._+_ S q (Scalar.neg S b)) witness)
          (Ring.addZeroLeft K (Scalar.neg S b)))))

zeroSumFirstDeterminedByTail :
  (K : Ring.ExactOrderedCommutativeRing) →
  {n : Nat} →
  (x : Fin (suc n) → SOf K) →
  Ring.sumFin (Ring.orderedScalar K) x
    ≡ Scalar.zero (Ring.orderedScalar K) →
  x zero ≡ Scalar.neg (Ring.orderedScalar K)
    (Ring.sumFin (Ring.orderedScalar K) (λ i → x (suc i)))
zeroSumFirstDeterminedByTail K x zeroSum =
  sumToZeroDeterminesFirst K
    (x zero)
    (Ring.sumFin (Ring.orderedScalar K) (λ i → x (suc i)))
    zeroSum

centredFirstRowDeterminedByRemainingRows :
  (K : Ring.ExactOrderedCommutativeRing) →
  {n p : Nat} → (M : Mean.ActualFiniteMean K (suc n) p) →
  (i : Fin p) →
  Matrix.entry (Centre.centredMatrix K (Mean.source M)) zero i
    ≡ Scalar.neg (Ring.orderedScalar K)
      (Ring.sumFin (Ring.orderedScalar K)
        (λ r → Matrix.entry
          (Centre.centredMatrix K (Mean.source M)) (suc r) i))
centredFirstRowDeterminedByRemainingRows K M i =
  zeroSumFirstDeterminedByTail K
    (λ r → Matrix.entry
      (Centre.centredMatrix K (Mean.source M)) r i)
    (Mean.sampleMeanDefiningEquation K M i)
