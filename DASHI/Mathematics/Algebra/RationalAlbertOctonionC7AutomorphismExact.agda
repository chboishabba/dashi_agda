module DASHI.Mathematics.Algebra.RationalAlbertOctonionC7AutomorphismExact where

------------------------------------------------------------------------
-- EXPLICIT ORDER-7 OCTONION AUTOMORPHISM AND ITS ALBERT LIFT
--
-- The repository octonion basis admits the unsigned Fano-plane permutation
--
--   e1->e2, e2->e4, e3->e6, e4->e5, e5->e7, e6->e1, e7->e3.
--
-- It has order seven and preserves the exact Cayley-Dickson product.  Applying
-- it simultaneously to x1,x2,x3 in H_3(O_Q) therefore gives a concrete C7
-- subgroup of the Albert automorphism group / cubic-norm stabilizer.  This is a
-- finite subgroup witness only: it is not promoted to full G2, F4, or E6.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Mathematics.Algebra.CayleyDicksonRationalOctonionExact as O
import DASHI.Mathematics.Algebra.RationalAlbertJordanExact as A
import DASHI.Mathematics.Algebra.RationalAlbertJordanUnitExact as U
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q

c7Octonion : O.RationalOctonion → O.RationalOctonion
c7Octonion
  (O.oct
    (Q.quat a0 a1 a2 a3)
    (Q.quat a4 a5 a6 a7)) =
  O.oct
    (Q.quat a0 a6 a1 a7)
    (Q.quat a2 a4 a3 a5)

c7OctonionOrderSeven : (value : O.RationalOctonion) →
  c7Octonion
    (c7Octonion
      (c7Octonion
        (c7Octonion
          (c7Octonion
            (c7Octonion
              (c7Octonion value))))))
  ≡ value
c7OctonionOrderSeven
  (O.oct (Q.quat _ _ _ _) (Q.quat _ _ _ _)) = refl

c7CommutesConjugation : (value : O.RationalOctonion) →
  c7Octonion (O.octonionConjugate value)
  ≡ O.octonionConjugate (c7Octonion value)
c7CommutesConjugation
  (O.oct (Q.quat _ _ _ _) (Q.quat _ _ _ _)) = refl

c7PreservesOctonionProduct : (left right : O.RationalOctonion) →
  c7Octonion (O._*o_ left right)
  ≡ O._*o_ (c7Octonion left) (c7Octonion right)
c7PreservesOctonionProduct
  (O.oct (Q.quat a0 a1 a2 a3) (Q.quat a4 a5 a6 a7))
  (O.oct (Q.quat b0 b1 b2 b3) (Q.quat b4 b5 b6 b7)) =
  O.octonionExt
    (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars))
    (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars))
  where
    vars : List ℚ
    vars =
      a0 ∷ a1 ∷ a2 ∷ a3 ∷ a4 ∷ a5 ∷ a6 ∷ a7 ∷
      b0 ∷ b1 ∷ b2 ∷ b3 ∷ b4 ∷ b5 ∷ b6 ∷ b7 ∷ []

c7PreservesOctonionNorm : (value : O.RationalOctonion) →
  O.octonionNormSq (c7Octonion value) ≡ O.octonionNormSq value
c7PreservesOctonionNorm
  (O.oct (Q.quat a0 a1 a2 a3) (Q.quat a4 a5 a6 a7)) =
  solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ a4 ∷ a5 ∷ a6 ∷ a7 ∷ [])

c7Albert : A.RationalAlbert → A.RationalAlbert
c7Albert (A.albert a b c x1 x2 x3) =
  A.albert a b c (c7Octonion x1) (c7Octonion x2) (c7Octonion x3)

c7AlbertOrderSeven : (value : A.RationalAlbert) →
  c7Albert
    (c7Albert
      (c7Albert
        (c7Albert
          (c7Albert
            (c7Albert
              (c7Albert value))))))
  ≡ value
c7AlbertOrderSeven (A.albert a b c x1 x2 x3) =
  U.albertExt refl refl refl
    (c7OctonionOrderSeven x1)
    (c7OctonionOrderSeven x2)
    (c7OctonionOrderSeven x3)

c7AlbertFixesUnit : c7Albert A.albertUnit ≡ A.albertUnit
c7AlbertFixesUnit = refl

c7AlbertPreservesJordan : (left right : A.RationalAlbert) →
  c7Albert (A.jordanProduct left right)
  ≡ A.jordanProduct (c7Albert left) (c7Albert right)
c7AlbertPreservesJordan
  (A.albert a b c
    (O.oct (Q.quat x10 x11 x12 x13) (Q.quat x14 x15 x16 x17))
    (O.oct (Q.quat x20 x21 x22 x23) (Q.quat x24 x25 x26 x27))
    (O.oct (Q.quat x30 x31 x32 x33) (Q.quat x34 x35 x36 x37)))
  (A.albert d e f
    (O.oct (Q.quat y10 y11 y12 y13) (Q.quat y14 y15 y16 y17))
    (O.oct (Q.quat y20 y21 y22 y23) (Q.quat y24 y25 y26 y27))
    (O.oct (Q.quat y30 y31 y32 y33) (Q.quat y34 y35 y36 y37))) =
  U.albertExt
    (solve vars) (solve vars) (solve vars)
    (O.octonionExt
      (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars))
      (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars)))
    (O.octonionExt
      (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars))
      (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars)))
    (O.octonionExt
      (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars))
      (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars)))
  where
    vars : List ℚ
    vars =
      a ∷ b ∷ c ∷
      x10 ∷ x11 ∷ x12 ∷ x13 ∷ x14 ∷ x15 ∷ x16 ∷ x17 ∷
      x20 ∷ x21 ∷ x22 ∷ x23 ∷ x24 ∷ x25 ∷ x26 ∷ x27 ∷
      x30 ∷ x31 ∷ x32 ∷ x33 ∷ x34 ∷ x35 ∷ x36 ∷ x37 ∷
      d ∷ e ∷ f ∷
      y10 ∷ y11 ∷ y12 ∷ y13 ∷ y14 ∷ y15 ∷ y16 ∷ y17 ∷
      y20 ∷ y21 ∷ y22 ∷ y23 ∷ y24 ∷ y25 ∷ y26 ∷ y27 ∷
      y30 ∷ y31 ∷ y32 ∷ y33 ∷ y34 ∷ y35 ∷ y36 ∷ y37 ∷ []

c7AlbertPreservesCubicNorm : (value : A.RationalAlbert) →
  A.cubicNorm (c7Albert value) ≡ A.cubicNorm value
c7AlbertPreservesCubicNorm
  (A.albert a b c
    (O.oct (Q.quat x10 x11 x12 x13) (Q.quat x14 x15 x16 x17))
    (O.oct (Q.quat x20 x21 x22 x23) (Q.quat x24 x25 x26 x27))
    (O.oct (Q.quat x30 x31 x32 x33) (Q.quat x34 x35 x36 x37))) =
  solve vars
  where
    vars : List ℚ
    vars =
      a ∷ b ∷ c ∷
      x10 ∷ x11 ∷ x12 ∷ x13 ∷ x14 ∷ x15 ∷ x16 ∷ x17 ∷
      x20 ∷ x21 ∷ x22 ∷ x23 ∷ x24 ∷ x25 ∷ x26 ∷ x27 ∷
      x30 ∷ x31 ∷ x32 ∷ x33 ∷ x34 ∷ x35 ∷ x36 ∷ x37 ∷ []

record C7ExceptionalBoundary : Set where
  constructor boundary
  field
    c7OctonionAutomorphismConstructed : Bool
    c7OctonionOrderSevenSourceWritten : Bool
    c7AlbertAutomorphismConstructed : Bool
    c7AlbertProductIntertwinerSourceWritten : Bool
    c7AlbertCubicNormIntertwinerSourceWritten : Bool
    fullG2AutomorphismGroupConstructed : Bool
    fullF4AutomorphismGroupConstructed : Bool
    fullE6NormStabilizerConstructed : Bool

open C7ExceptionalBoundary public

canonicalBoundary : C7ExceptionalBoundary
canonicalBoundary = boundary true true true true true false false false
