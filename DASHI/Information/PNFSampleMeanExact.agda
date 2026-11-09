module DASHI.Information.PNFSampleMeanExact where

-- Exact source-owned finite means.  This is not a random-matrix theorem.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Fin.Base using (Fin)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Physics.Closure.NSTriadKNExactOrderedScalar as Scalar
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffInnerProduct as Ring
import DASHI.Information.PNFFiniteCovarianceEconomicsExact as Matrix
import DASHI.Information.PNFCentredCovarianceExact as Centre

private
  SOf : Ring.ExactOrderedCommutativeRing → Set
  SOf K = Scalar.Scalar (Ring.orderedScalar K)

sumConstantValue :
  (K : Ring.ExactOrderedCommutativeRing) →
  {n : Nat} → (a : SOf K) →
  Ring.sumFin (Ring.orderedScalar K) (λ (_ : Fin n) → a)
  ≡ Scalar._*_ (Ring.orderedScalar K)
      (Matrix.dimensionScalar K n) a
sumConstantValue K {n} a =
  let S = Ring.orderedScalar K in
  trans
    (Ring.sumFinCong S
      (λ i → sym (Ring.mulOneLeft K a)))
    (trans
      (Ring.sumFinMulLeft K a
        (λ (_ : Fin n) → Scalar.one S))
      (trans
        (cong (Scalar._*_ S a) (Matrix.sumConstantOne K {n}))
        (Ring.mulCommutative K a (Matrix.dimensionScalar K n))))

record ActualFiniteMean
  (K : Ring.ExactOrderedCommutativeRing)
  (n p : Nat) : Set₁ where
  private
    S = Ring.orderedScalar K
  field
    source : Centre.FiniteCentredData K n p
    sampleCount : Scalar.Scalar S
    sampleCountIsLength :
      sampleCount ≡ Matrix.dimensionScalar K n
    actualMean :
      (i : Fin p) →
      Ring.sumFin S (λ r → Matrix.entry (Centre.raw source) r i)
      ≡ Scalar._*_ S sampleCount (Centre.columnMean source i)

open ActualFiniteMean public

sampleMeanDefiningEquation :
  (K : Ring.ExactOrderedCommutativeRing) →
  {n p : Nat} → (M : ActualFiniteMean K n p) →
  (i : Fin p) →
  Ring.sumFin (Ring.orderedScalar K)
    (λ r → Matrix.entry (Centre.centredMatrix K (source M)) r i)
  ≡ Scalar.zero (Ring.orderedScalar K)
sampleMeanDefiningEquation K {n} M i =
  let S = Ring.orderedScalar K
      mu = Centre.columnMean (source M) i
      rawCol = λ r → Matrix.entry (Centre.raw (source M)) r i
      countMu = Scalar._*_ S (sampleCount M) mu
  in
  trans
    (Ring.sumFinAdd K rawCol (λ (_ : Fin n) → Scalar.neg S mu))
    (trans
      (cong (Scalar._+_ S (Ring.sumFin S rawCol))
        (trans
          (Ring.sumFinNeg K (λ (_ : Fin n) → mu))
          (cong (Scalar.neg S)
            (trans
              (sumConstantValue K {n} mu)
              (cong (λ k → Scalar._*_ S k mu)
                (sym (sampleCountIsLength M))))))
      (trans
        (cong (λ q → Scalar._+_ S q (Scalar.neg S countMu))
          (actualMean M i))
        (trans
          (Ring.addCommutative K countMu (Scalar.neg S countMu))
          (Ring.addInverseLeft K countMu)))))
