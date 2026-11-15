module DASHI.Information.PNFCovarianceQuadraticIdentityExact where

-- Same-operator v^T C v = scaled row-wise sum of squares.
-- Reuses the actual finite Gram, finite Fubini and exact ring algebra.

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Fin.Base using (Fin)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Physics.Closure.NSTriadKNExactOrderedScalar as Scalar
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffInnerProduct as Ring
import DASHI.Information.PNFFiniteCovarianceEconomicsExact as Matrix
import DASHI.Information.PNFFiniteGramPositiveExact as Positive
import DASHI.Information.PNFCentredCovarianceExact as Centre
import DASHI.Information.PNFFiniteSumExchangeExact as Exchange
import DASHI.Information.PNFFiniteBilinearExpansionExact as Bilinear
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffOrbitGramAssembly as ExistingPSD

private
  SOf : Ring.ExactOrderedCommutativeRing → Set
  SOf K = Scalar.Scalar (Ring.orderedScalar K)

gramAction :
  (K : Ring.ExactOrderedCommutativeRing) →
  {n p : Nat} → (X : Matrix.FiniteMatrix K n p) →
  (v : Fin p → SOf K) → Fin p → SOf K
gramAction K X v i =
  Ring.sumFin (Ring.orderedScalar K)
    (λ j → Scalar._*_ (Ring.orderedScalar K)
      (Matrix.gram K X i j) (v j))

gramActionEqualsRowProjection :
  (K : Ring.ExactOrderedCommutativeRing) →
  {n p : Nat} → (X : Matrix.FiniteMatrix K n p) →
  (v : Fin p → SOf K) → (i : Fin p) →
  gramAction K X v i ≡
    Ring.sumFin (Ring.orderedScalar K)
      (λ r → Scalar._*_ (Ring.orderedScalar K)
        (Matrix.entry X r i) (Positive.projection K X v r))
gramActionEqualsRowProjection K X v i =
  let S = Ring.orderedScalar K in
  trans
    (Ring.sumFinCong S
      (λ j → sym (Bilinear.sumFinMulRight K
        (λ r → Scalar._*_ S (Matrix.entry X r i)
                                (Matrix.entry X r j))
        (v j))))
    (trans
      (Exchange.finiteSumExchange K
        (λ j r → Scalar._*_ S
          (Scalar._*_ S (Matrix.entry X r i)
                          (Matrix.entry X r j))
          (v j)))
      (Ring.sumFinCong S
        (λ r →
          trans
            (Ring.sumFinCong S
              (λ j → Ring.mulAssociative K
                (Matrix.entry X r i)
                (Matrix.entry X r j) (v j)))
            (Ring.sumFinMulLeft K (Matrix.entry X r i)
              (λ j → Scalar._*_ S
                (Matrix.entry X r j) (v j))))))

unscaledGramQuadratic :
  (K : Ring.ExactOrderedCommutativeRing) →
  {n p : Nat} → (X : Matrix.FiniteMatrix K n p) →
  (v : Fin p → SOf K) → SOf K
unscaledGramQuadratic K X v =
  Ring.sumFin (Ring.orderedScalar K)
    (λ i → Scalar._*_ (Ring.orderedScalar K)
      (v i) (gramAction K X v i))

unscaledGramQuadraticEqualsSquares :
  (K : Ring.ExactOrderedCommutativeRing) →
  {n p : Nat} → (X : Matrix.FiniteMatrix K n p) →
  (v : Fin p → SOf K) →
  unscaledGramQuadratic K X v ≡ Positive.gramQuadratic K X v
unscaledGramQuadraticEqualsSquares K X v =
  let S = Ring.orderedScalar K in
  trans
    (Ring.sumFinCong S
      (λ i → cong (Scalar._*_ S (v i))
        (gramActionEqualsRowProjection K X v i)))
    (trans
      (Exchange.finiteSumExchange K
        (λ i r → Scalar._*_ S (v i)
          (Scalar._*_ S (Matrix.entry X r i)
            (Positive.projection K X v r))))
      (Ring.sumFinCong S
        (λ r →
          trans
            (Ring.sumFinCong S
              (λ i → sym (Ring.mulAssociative K
                (v i) (Matrix.entry X r i)
                (Positive.projection K X v r))))
            (trans
              (Bilinear.sumFinMulRight K
                (λ i → Scalar._*_ S (v i) (Matrix.entry X r i))
                (Positive.projection K X v r))
              (cong (λ a → Scalar._*_ S a
                  (Positive.projection K X v r))
                (Ring.sumFinCong S
                  (λ i → Ring.mulCommutative K
                    (v i) (Matrix.entry X r i))))))))

-- The vector quadratic form of the *actual* scaled covariance operator.
covarianceOperatorQuadratic :
  (K : Ring.ExactOrderedCommutativeRing) →
  {n p : Nat} → (X : Centre.FiniteCentredData K n p) →
  (scale : SOf K) → (v : Fin p → SOf K) → SOf K
covarianceOperatorQuadratic K X scale v =
  Ring.sumFin (Ring.orderedScalar K)
    (λ i → Scalar._*_ (Ring.orderedScalar K) (v i)
      (Ring.sumFin (Ring.orderedScalar K)
        (λ j → Scalar._*_ (Ring.orderedScalar K)
          (Centre.scaledCovariance K X scale i j) (v j))))

-- A scalar moves through a finite bilinear quadratic via associativity
-- and commutativity, then through each finite sum by sumFinMulLeft.
covarianceScaleOut :
  (K : Ring.ExactOrderedCommutativeRing) →
  {n p : Nat} → (X : Centre.FiniteCentredData K n p) →
  (scale : SOf K) → (v : Fin p → SOf K) →
  covarianceOperatorQuadratic K X scale v ≡
  Scalar._*_ (Ring.orderedScalar K) scale
    (unscaledGramQuadratic K (Centre.centredMatrix K X) v)
covarianceScaleOut K X scale v =
  let S = Ring.orderedScalar K
      Y = Centre.centredMatrix K X
  in
  trans
    (Ring.sumFinCong S
      (λ i →
        cong (Scalar._*_ S (v i))
          (trans
            (Ring.sumFinCong S
              (λ j → Ring.mulAssociative K scale
                (Matrix.gram K Y i j) (v j)))
            (Ring.sumFinMulLeft K scale
              (λ j → Scalar._*_ S (Matrix.gram K Y i j) (v j))))))
    (trans
      (Ring.sumFinCong S
        (λ i →
          trans
            (Ring.mulCommutative K (v i)
              (Scalar._*_ S scale (gramAction K Y v i)))
            (trans
              (sym (Ring.mulAssociative K scale
                (gramAction K Y v i) (v i)))
              (cong (Scalar._*_ S scale)
                (Ring.mulCommutative K
                  (gramAction K Y v i) (v i))))))
      (Ring.sumFinMulLeft K scale
        (λ i → Scalar._*_ S (v i) (gramAction K Y v i))))

scaledCovarianceQuadraticEqualsScaledGramQuadratic :
  (K : Ring.ExactOrderedCommutativeRing) →
  {n p : Nat} → (X : Centre.FiniteCentredData K n p) →
  (scale : SOf K) → (v : Fin p → SOf K) →
  covarianceOperatorQuadratic K X scale v ≡
  Centre.scaledGramQuadratic K X scale v
scaledCovarianceQuadraticEqualsScaledGramQuadratic K X scale v =
  trans (covarianceScaleOut K X scale v)
    (cong (Scalar._*_ (Ring.orderedScalar K) scale)
      (unscaledGramQuadraticEqualsSquares K
        (Centre.centredMatrix K X) v))

-- End-to-end same-operator positive semidefiniteness.
-- It derives the operator quadratic's positivity by transporting the
-- canonical DASHI finite Gram PSD order authority across the exact equality.
covarianceOperatorPositiveSemidefinite :
  (K : Ring.ExactOrderedCommutativeRing) →
  (O : ExistingPSD.FiniteGramOrderAuthority K) →
  {n p : Nat} → (X : Centre.FiniteCentredData K n p) →
  (scale : SOf K) →
  Scalar._≤_ (Ring.orderedScalar K)
    (Scalar.zero (Ring.orderedScalar K)) scale →
  (v : Fin p → SOf K) →
  Scalar._≤_ (Ring.orderedScalar K)
    (Scalar.zero (Ring.orderedScalar K))
    (covarianceOperatorQuadratic K X scale v)
covarianceOperatorPositiveSemidefinite K O X scale scaleNonnegative v
  rewrite scaledCovarianceQuadraticEqualsScaledGramQuadratic
    K X scale v =
  Centre.centredCovarianceGramPSDFromExisting
    K O X scale scaleNonnegative v
