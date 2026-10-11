module DASHI.Mathematics.Algebra.RationalAlbertS3AutomorphismExact where

------------------------------------------------------------------------
-- EXPLICIT S3 MATRIX-INDEX SUBGROUP OF THE RATIONAL ALBERT AUTOMORPHISMS
--
-- Even permutations of the three Hermitian indices permute (a1,a2,a3) and
-- (x1,x2,x3) in the same way.  Odd permutations additionally conjugate all
-- three off-diagonal octonions.  It suffices to use:
--
--   r(a,b,c;x1,x2,x3) = (b,c,a;x2,x3,x1),      r^3 = 1
--   s(a,b,c;x1,x2,x3) = (a,c,b;bar x1,bar x3,bar x2), s^2 = 1
--   s r s = r^2.
--
-- Both generators preserve the Jordan product, the distinguished unit and the
-- cubic norm.  This is a concrete S3 subgroup of the Albert automorphism group
-- and hence also of the cubic-norm stabilizer.  It is not promoted to the full
-- exceptional groups F4 or E6.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Mathematics.Algebra.RationalAlbertJordanExact as A
import DASHI.Mathematics.Algebra.RationalAlbertJordanUnitExact as U
import DASHI.Mathematics.Algebra.RationalAlbertCyclicAutomorphismExact as C3
import DASHI.Mathematics.Algebra.CayleyDicksonRationalOctonionExact as O
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q

swap23Albert : A.RationalAlbert → A.RationalAlbert
swap23Albert (A.albert a b c x1 x2 x3) =
  A.albert
    a c b
    (O.octonionConjugate x1)
    (O.octonionConjugate x3)
    (O.octonionConjugate x2)

swap23Squared : (value : A.RationalAlbert) →
  swap23Albert (swap23Albert value) ≡ value
swap23Squared (A.albert a b c x1 x2 x3) =
  U.albertExt
    refl refl refl
    (O.octonionConjugateInvolutive x1)
    (O.octonionConjugateInvolutive x2)
    (O.octonionConjugateInvolutive x3)

swap23FixesUnit : swap23Albert A.albertUnit ≡ A.albertUnit
swap23FixesUnit = refl

swap23PreservesJordan : (left right : A.RationalAlbert) →
  swap23Albert (A.jordanProduct left right)
  ≡ A.jordanProduct (swap23Albert left) (swap23Albert right)
swap23PreservesJordan
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

swap23PreservesCubicNorm : (value : A.RationalAlbert) →
  A.cubicNorm (swap23Albert value) ≡ A.cubicNorm value
swap23PreservesCubicNorm
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

srsIsRSquared : (value : A.RationalAlbert) →
  swap23Albert (C3.rotateAlbert (swap23Albert value))
  ≡ C3.rotateAlbertTwice value
srsIsRSquared (A.albert a b c x1 x2 x3) =
  U.albertExt
    refl refl refl
    (O.octonionConjugateInvolutive x3)
    (O.octonionConjugateInvolutive x1)
    (O.octonionConjugateInvolutive x2)

record S3AlbertBoundary : Set where
  constructor boundary
  field
    cyclicGeneratorOrderThree : Bool
    transpositionGeneratorOrderTwo : Bool
    braidRelationSourceWritten : Bool
    bothGeneratorsFixUnit : Bool
    bothGeneratorsPreserveJordanProduct : Bool
    bothGeneratorsPreserveCubicNorm : Bool
    s3MatrixIndexAutomorphismSubgroupConstructed : Bool
    fullF4AutomorphismGroupConstructed : Bool
    fullE6NormStabilizerConstructed : Bool

open S3AlbertBoundary public

canonicalBoundary : S3AlbertBoundary
canonicalBoundary =
  boundary true true true true true true true false false
