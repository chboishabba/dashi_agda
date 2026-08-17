module DASHI.Physics.Closure.NSTriadKNLerayComplexScalarLinearityRound73Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Authors: DASHI repository contributors.
-- Title: exact C3 complex/Hermitian algebra used below.
-- DOI: not applicable to repository-original finite algebra.
--
-- ROUND73 / LERAY COMMUTES WITH COMPLEX SCALARS
--
-- The literal projected interaction is
--
--   -i P_k [ (u_p dot q) u_q ].
--
-- To expose the source-native low/high factorization before any rational
-- collapse we need the exact algebraic identity
--
--   P_k (a v) = a P_k(v).
--
-- This file proves it directly from the repository's literal Leray formula
--
--   P_k v = v - |k|^{-2} (k dot v) k,
--
-- using only exact complex/C3 algebra.  No analytic estimate, positivity,
-- norm bound, or new projection receipt is introduced.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3AlgebraLaws as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianScalingLaws as Scaling
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAdditiveLaws as Additive

complexMultiplyNegateRight :
  ∀ {r} {F : C3.RealField r}
    (scalar value : C3.Complex F) →
  C3.complexMultiply scalar (C3.complexNegate value)
  ≡ C3.complexNegate (C3.complexMultiply scalar value)
complexMultiplyNegateRight {F = F} scalar value =
  trans
    (cong (C3.complexMultiply scalar)
      (sym (Additive.complexMultiplyMinusOneLeft value)))
    (trans
      (Scaling.complexMultiplyAssociative scalar (Additive.minusOne F) value)
      (trans
        (cong
          (λ first → C3.complexMultiply first value)
          (trans
            (Algebra.complexMultiplyCommutative scalar (Additive.minusOne F))
            (Additive.complexMultiplyMinusOneLeft scalar)))
        (sym (Additive.complexMultiplyMinusOneLeft
          (C3.complexMultiply scalar value)))))

complex3ScaleAssociative :
  ∀ {r} {F : C3.RealField r}
    (left right : C3.Complex F)
    (value : C3.Complex3 F) →
  C3.complex3Scale left (C3.complex3Scale right value)
  ≡ C3.complex3Scale (C3.complexMultiply left right) value
complex3ScaleAssociative left right (C3.complex3 x y z)
  rewrite Scaling.complexMultiplyAssociative left right x
        | Scaling.complexMultiplyAssociative left right y
        | Scaling.complexMultiplyAssociative left right z = refl

complex3ScaleNegate :
  ∀ {r} {F : C3.RealField r}
    (scalar : C3.Complex F)
    (value : C3.Complex3 F) →
  C3.complex3Scale scalar (C3.complex3Negate value)
  ≡ C3.complex3Negate (C3.complex3Scale scalar value)
complex3ScaleNegate scalar (C3.complex3 x y z)
  rewrite complexMultiplyNegateRight scalar x
        | complexMultiplyNegateRight scalar y
        | complexMultiplyNegateRight scalar z = refl

complex3ScaleAdd :
  ∀ {r} {F : C3.RealField r}
    (scalar : C3.Complex F)
    (left right : C3.Complex3 F) →
  C3.complex3Scale scalar (C3.complex3Add left right)
  ≡ C3.complex3Add
      (C3.complex3Scale scalar left)
      (C3.complex3Scale scalar right)
complex3ScaleAdd scalar
    (C3.complex3 lx ly lz) (C3.complex3 rx ry rz)
  rewrite Algebra.complexMultiplyDistributesLeft scalar lx rx
        | Algebra.complexMultiplyDistributesLeft scalar ly ry
        | Algebra.complexMultiplyDistributesLeft scalar lz rz = refl

complex3ScaleSubtract :
  ∀ {r} {F : C3.RealField r}
    (scalar : C3.Complex F)
    (left right : C3.Complex3 F) →
  C3.complex3Scale scalar (C3.complex3Subtract left right)
  ≡ C3.complex3Subtract
      (C3.complex3Scale scalar left)
      (C3.complex3Scale scalar right)
complex3ScaleSubtract scalar left right =
  trans
    (complex3ScaleAdd scalar left (C3.complex3Negate right))
    (cong
      (C3.complex3Add (C3.complex3Scale scalar left))
      (complex3ScaleNegate scalar right))

lerayProjectComplexScale :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (mode : Z3.FourierMode)
    (scalar : C3.Complex F)
    (value : C3.Complex3 F) →
  C3.lerayProject3 E I mode (C3.complex3Scale scalar value)
  ≡ C3.complex3Scale scalar (C3.lerayProject3 E I mode value)
lerayProjectComplexScale {F = F} E I mode scalar value =
  let
    inverse = C3.realEmbed F (C3.inverseNormSquared I mode)
    wave = C3.modeVector E mode
    dot = C3.bilinearDot3 wave value

    scaledDot :
      C3.bilinearDot3 wave (C3.complex3Scale scalar value)
      ≡ C3.complexMultiply scalar dot
    scaledDot = Scaling.bilinearDot3ScaleRight scalar wave value

    correctionScale :
      C3.complex3Scale
        (C3.complexMultiply inverse
          (C3.bilinearDot3 wave (C3.complex3Scale scalar value)))
        wave
      ≡
      C3.complex3Scale scalar
        (C3.complex3Scale (C3.complexMultiply inverse dot) wave)
    correctionScale =
      trans
        (cong
          (λ coefficient → C3.complex3Scale coefficient wave)
          (trans
            (cong (C3.complexMultiply inverse) scaledDot)
            (trans
              (Scaling.complexMultiplyAssociative inverse scalar dot)
              (trans
                (cong
                  (λ first → C3.complexMultiply first dot)
                  (Algebra.complexMultiplyCommutative inverse scalar))
                (sym
                  (Scaling.complexMultiplyAssociative
                    scalar inverse dot))))))
        (sym
          (complex3ScaleAssociative
            scalar (C3.complexMultiply inverse dot) wave))
  in
  trans
    (cong
      (C3.complex3Subtract (C3.complex3Scale scalar value))
      correctionScale)
    (sym
      (complex3ScaleSubtract
        scalar value
        (C3.complex3Scale (C3.complexMultiply inverse dot) wave)))

round73LerayComplexScalarLinearityConstructed : Bool
round73LerayComplexScalarLinearityConstructed = true

round73LerayComplexScalarLinearityConstructedIsTrue :
  round73LerayComplexScalarLinearityConstructed ≡ true
round73LerayComplexScalarLinearityConstructedIsTrue = refl
