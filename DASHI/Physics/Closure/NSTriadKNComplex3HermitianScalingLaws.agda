module DASHI.Physics.Closure.NSTriadKNComplex3HermitianScalingLaws where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: DASHI repository contributors.
-- Title: "Complex multiplication associativity and Hermitian scaling laws
-- for the exact Stage-3 C3 carrier".
-- Venue/year: DASHI formal development, 2026.
-- DOI: not applicable; these are repository-original consequences of the
-- exact commutative RealField interface.
-- Uses: real-field associativity, commutativity, distributivity and additive
-- inverses; the literal complex product; coordinatewise C3 scaling; and the
-- Hermitian convention <u,v> = conjugate(u) dot v.
-- Relationship: instantiates the previously explicit HermitianScalingCutset.
-- The proof reduces each complex associativity coordinate to one four-term
-- commutative-ring permutation, then derives bilinear-dot and Hermitian
-- scale-left/scale-right laws.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3AlgebraLaws as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAlgebraProgram as Hermitian

realFourTermRotate :
  ∀ {r} (F : C3.RealField r)
    (a d b c : C3.Carrier F) →
  C3.add F (C3.add F a d) (C3.add F b c)
  ≡ C3.add F (C3.add F a b) (C3.add F c d)
realFourTermRotate F a d b c =
  trans
    (Algebra.realInterchange F a d b c)
    (cong (C3.add F (C3.add F a b))
      (C3.addCommutative F d c))

complexMultiplyAssociative :
  ∀ {r} {F : C3.RealField r}
    (a b c : C3.Complex F) →
  C3.complexMultiply (C3.complexMultiply a b) c
  ≡ C3.complexMultiply a (C3.complexMultiply b c)
complexMultiplyAssociative {F = F}
  (C3.complex ar ai)
  (C3.complex br bi)
  (C3.complex cr ci) =
  Algebra.cong₂ C3.complex realCoordinate imaginaryCoordinate
  where
    realA realB realC realD : C3.Carrier F
    realA = C3.multiply F ar (C3.multiply F br cr)
    realB = C3.multiply F ar (C3.multiply F bi ci)
    realC = C3.multiply F ai (C3.multiply F br ci)
    realD = C3.multiply F ai (C3.multiply F bi cr)

    leftRealFirst :
      C3.multiply F
        (C3.add F
          (C3.multiply F ar br)
          (C3.negate F (C3.multiply F ai bi)))
        cr
      ≡ C3.add F realA (C3.negate F realD)
    leftRealFirst =
      trans
        (Algebra.realDistributeRight F
          (C3.multiply F ar br)
          (C3.negate F (C3.multiply F ai bi))
          cr)
        (Algebra.cong₂ (C3.add F)
          (C3.multiplyAssociative F ar br cr)
          (trans
            (sym (Algebra.realNegateMultiplyLeft F
              (C3.multiply F ai bi) cr))
            (cong (C3.negate F)
              (C3.multiplyAssociative F ai bi cr))))

    leftRealSecond :
      C3.negate F
        (C3.multiply F
          (C3.add F
            (C3.multiply F ar bi)
            (C3.multiply F ai br))
          ci)
      ≡ C3.add F (C3.negate F realB) (C3.negate F realC)
    leftRealSecond =
      trans
        (cong (C3.negate F)
          (Algebra.realDistributeRight F
            (C3.multiply F ar bi)
            (C3.multiply F ai br)
            ci))
        (trans
          (Algebra.realNegateAdd F
            (C3.multiply F (C3.multiply F ar bi) ci)
            (C3.multiply F (C3.multiply F ai br) ci))
          (Algebra.cong₂ (C3.add F)
            (cong (C3.negate F)
              (C3.multiplyAssociative F ar bi ci))
            (cong (C3.negate F)
              (C3.multiplyAssociative F ai br ci))))

    rightRealFirst :
      C3.multiply F ar
        (C3.add F
          (C3.multiply F br cr)
          (C3.negate F (C3.multiply F bi ci)))
      ≡ C3.add F realA (C3.negate F realB)
    rightRealFirst =
      trans
        (C3.distributeLeft F ar
          (C3.multiply F br cr)
          (C3.negate F (C3.multiply F bi ci)))
        (Algebra.cong₂ (C3.add F)
          refl
          (sym (Algebra.realNegateMultiplyRight F ar
            (C3.multiply F bi ci))))

    rightRealSecond :
      C3.negate F
        (C3.multiply F ai
          (C3.add F
            (C3.multiply F br ci)
            (C3.multiply F bi cr)))
      ≡ C3.add F (C3.negate F realC) (C3.negate F realD)
    rightRealSecond =
      trans
        (cong (C3.negate F)
          (C3.distributeLeft F ai
            (C3.multiply F br ci)
            (C3.multiply F bi cr)))
        (Algebra.realNegateAdd F realC realD)

    realCoordinate :
      C3.add F
        (C3.multiply F
          (C3.add F
            (C3.multiply F ar br)
            (C3.negate F (C3.multiply F ai bi)))
          cr)
        (C3.negate F
          (C3.multiply F
            (C3.add F
              (C3.multiply F ar bi)
              (C3.multiply F ai br))
            ci))
      ≡
      C3.add F
        (C3.multiply F ar
          (C3.add F
            (C3.multiply F br cr)
            (C3.negate F (C3.multiply F bi ci))))
        (C3.negate F
          (C3.multiply F ai
            (C3.add F
              (C3.multiply F br ci)
              (C3.multiply F bi cr))))
    realCoordinate =
      trans
        (Algebra.cong₂ (C3.add F) leftRealFirst leftRealSecond)
        (trans
          (realFourTermRotate F
            realA
            (C3.negate F realD)
            (C3.negate F realB)
            (C3.negate F realC))
          (sym (Algebra.cong₂ (C3.add F)
            rightRealFirst rightRealSecond)))

    imagA imagB imagC imagD : C3.Carrier F
    imagA = C3.multiply F ar (C3.multiply F br ci)
    imagB = C3.multiply F ar (C3.multiply F bi cr)
    imagC = C3.multiply F ai (C3.multiply F br cr)
    imagD = C3.multiply F ai (C3.multiply F bi ci)

    leftImagFirst :
      C3.multiply F
        (C3.add F
          (C3.multiply F ar br)
          (C3.negate F (C3.multiply F ai bi)))
        ci
      ≡ C3.add F imagA (C3.negate F imagD)
    leftImagFirst =
      trans
        (Algebra.realDistributeRight F
          (C3.multiply F ar br)
          (C3.negate F (C3.multiply F ai bi))
          ci)
        (Algebra.cong₂ (C3.add F)
          (C3.multiplyAssociative F ar br ci)
          (trans
            (sym (Algebra.realNegateMultiplyLeft F
              (C3.multiply F ai bi) ci))
            (cong (C3.negate F)
              (C3.multiplyAssociative F ai bi ci))))

    leftImagSecond :
      C3.multiply F
        (C3.add F
          (C3.multiply F ar bi)
          (C3.multiply F ai br))
        cr
      ≡ C3.add F imagB imagC
    leftImagSecond =
      trans
        (Algebra.realDistributeRight F
          (C3.multiply F ar bi)
          (C3.multiply F ai br)
          cr)
        (Algebra.cong₂ (C3.add F)
          (C3.multiplyAssociative F ar bi cr)
          (C3.multiplyAssociative F ai br cr))

    rightImagFirst :
      C3.multiply F ar
        (C3.add F
          (C3.multiply F br ci)
          (C3.multiply F bi cr))
      ≡ C3.add F imagA imagB
    rightImagFirst =
      C3.distributeLeft F ar
        (C3.multiply F br ci)
        (C3.multiply F bi cr)

    rightImagSecond :
      C3.multiply F ai
        (C3.add F
          (C3.multiply F br cr)
          (C3.negate F (C3.multiply F bi ci)))
      ≡ C3.add F imagC (C3.negate F imagD)
    rightImagSecond =
      trans
        (C3.distributeLeft F ai
          (C3.multiply F br cr)
          (C3.negate F (C3.multiply F bi ci)))
        (Algebra.cong₂ (C3.add F)
          refl
          (sym (Algebra.realNegateMultiplyRight F ai
            (C3.multiply F bi ci))))

    imaginaryCoordinate :
      C3.add F
        (C3.multiply F
          (C3.add F
            (C3.multiply F ar br)
            (C3.negate F (C3.multiply F ai bi)))
          ci)
        (C3.multiply F
          (C3.add F
            (C3.multiply F ar bi)
            (C3.multiply F ai br))
          cr)
      ≡
      C3.add F
        (C3.multiply F ar
          (C3.add F
            (C3.multiply F br ci)
            (C3.multiply F bi cr)))
        (C3.multiply F ai
          (C3.add F
            (C3.multiply F br cr)
            (C3.negate F (C3.multiply F bi ci))))
    imaginaryCoordinate =
      trans
        (Algebra.cong₂ (C3.add F) leftImagFirst leftImagSecond)
        (trans
          (realFourTermRotate F
            imagA
            (C3.negate F imagD)
            imagB
            imagC)
          (sym (Algebra.cong₂ (C3.add F)
            rightImagFirst rightImagSecond)))

complex3ConjugateScale :
  ∀ {r} {F : C3.RealField r}
    (scalar : C3.Complex F)
    (value : C3.Complex3 F) →
  C3.complex3Conjugate (C3.complex3Scale scalar value)
  ≡ C3.complex3Scale
      (C3.complexConjugate scalar)
      (C3.complex3Conjugate value)
complex3ConjugateScale scalar (C3.complex3 vx vy vz)
  rewrite Hermitian.complexConjugateMultiply scalar vx
        | Hermitian.complexConjugateMultiply scalar vy
        | Hermitian.complexConjugateMultiply scalar vz = refl

bilinearDot3ScaleLeft :
  ∀ {r} {F : C3.RealField r}
    (scalar : C3.Complex F)
    (u v : C3.Complex3 F) →
  C3.bilinearDot3 (C3.complex3Scale scalar u) v
  ≡ C3.complexMultiply scalar (C3.bilinearDot3 u v)
bilinearDot3ScaleLeft scalar
  (C3.complex3 ux uy uz)
  (C3.complex3 vx vy vz)
  rewrite complexMultiplyAssociative scalar ux vx
        | complexMultiplyAssociative scalar uy vy
        | complexMultiplyAssociative scalar uz vz =
  trans
    (cong
      (λ first →
        C3.complexAdd first
          (C3.complexMultiply scalar (C3.complexMultiply uz vz)))
      (sym (Algebra.complexMultiplyDistributesLeft scalar
        (C3.complexMultiply ux vx)
        (C3.complexMultiply uy vy))))
    (sym (Algebra.complexMultiplyDistributesLeft scalar
      (C3.complexAdd
        (C3.complexMultiply ux vx)
        (C3.complexMultiply uy vy))
      (C3.complexMultiply uz vz)))

bilinearDot3ScaleRight :
  ∀ {r} {F : C3.RealField r}
    (scalar : C3.Complex F)
    (u v : C3.Complex3 F) →
  C3.bilinearDot3 u (C3.complex3Scale scalar v)
  ≡ C3.complexMultiply scalar (C3.bilinearDot3 u v)
bilinearDot3ScaleRight scalar u v =
  trans
    (Algebra.bilinearDot3Commutative u (C3.complex3Scale scalar v))
    (trans
      (bilinearDot3ScaleLeft scalar v u)
      (cong (C3.complexMultiply scalar)
        (Algebra.bilinearDot3Commutative v u)))

hermitianPairingScaleLeft :
  ∀ {r} {F : C3.RealField r}
    (scalar : C3.Complex F)
    (u v : C3.Complex3 F) →
  C3.hermitianPairing3 (C3.complex3Scale scalar u) v
  ≡ C3.complexMultiply
      (C3.complexConjugate scalar)
      (C3.hermitianPairing3 u v)
hermitianPairingScaleLeft scalar u v =
  trans
    (cong (λ first → C3.bilinearDot3 first v)
      (complex3ConjugateScale scalar u))
    (bilinearDot3ScaleLeft
      (C3.complexConjugate scalar)
      (C3.complex3Conjugate u)
      v)

hermitianPairingScaleRight :
  ∀ {r} {F : C3.RealField r}
    (scalar : C3.Complex F)
    (u v : C3.Complex3 F) →
  C3.hermitianPairing3 u (C3.complex3Scale scalar v)
  ≡ C3.complexMultiply scalar (C3.hermitianPairing3 u v)
hermitianPairingScaleRight scalar u v =
  bilinearDot3ScaleRight scalar (C3.complex3Conjugate u) v

complex3HermitianScalingLaws :
  ∀ {r} (F : C3.RealField r) → Hermitian.HermitianScalingCutset F
complex3HermitianScalingLaws F = record
  { complexMultiplyAssociative = complexMultiplyAssociative
  ; hermitianPairingScaleLeft = hermitianPairingScaleLeft
  ; hermitianPairingScaleRight = hermitianPairingScaleRight
  }

complexMultiplicationAssociativityClosed : Bool
complexMultiplicationAssociativityClosed = true

complexMultiplicationAssociativityClosedIsTrue :
  complexMultiplicationAssociativityClosed ≡ true
complexMultiplicationAssociativityClosedIsTrue = refl

hermitianScalingLawsClosed : Bool
hermitianScalingLawsClosed = true

hermitianScalingLawsClosedIsTrue : hermitianScalingLawsClosed ≡ true
hermitianScalingLawsClosedIsTrue = refl
