module DASHI.Mathematics.Algebra.RationalAlbertJordanExact where

------------------------------------------------------------------------
-- RATIONAL ALBERT CARRIER OVER THE REPOSITORY'S CHECKED OCTONIONS
--
-- PRIMARY MATHEMATICAL CONTEXT
--   Standard exceptional Jordan algebra H_3(O): 3x3 Hermitian octonion
--   matrices with Jordan product X o Y = (XY + YX)/2 and cubic determinant.
--
-- DASHI CONTRIBUTION
--   Instantiate that carrier over the repository's exact rational octonions.
--   This pays the concrete 27-coordinate carrier, product, distinguished unit,
--   trace and cubic-norm definitions.  The universal Jordan identity and the
--   F4/E6 action recognitions remain explicit later proof obligations.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _/_)

import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Mathematics.Algebra.CayleyDicksonRationalOctonionExact as O

qHalf : ℚ
qHalf = + 1 / 2

scalarO : ℚ → O.RationalOctonion
scalarO q = O.oct (Q.quat q 0ℚ 0ℚ 0ℚ) Q.zeroQ

octRealPart : O.RationalOctonion → ℚ
octRealPart (O.oct (Q.quat a _ _ _) _) = a

add3O : O.RationalOctonion → O.RationalOctonion → O.RationalOctonion → O.RationalOctonion
add3O a b c = O._+o_ (O._+o_ a b) c

halfO : O.RationalOctonion → O.RationalOctonion
halfO value = O._*o_ (scalarO qHalf) value

record RationalAlbert : Set where
  constructor albert
  field
    diag1 diag2 diag3 : ℚ
    x1 x2 x3 : O.RationalOctonion

open RationalAlbert public

rationalAlbertDimension : Nat
rationalAlbertDimension = 3 + (3 * 8)

rationalAlbertDimensionIs27 : rationalAlbertDimension ≡ 27
rationalAlbertDimensionIs27 = refl

------------------------------------------------------------------------
-- Hermitian matrix convention
--
-- [ a1        x3        conj x2 ]
-- [ conj x3   a2        x1      ]
-- [ x2        conj x1   a3      ]
------------------------------------------------------------------------

mul00 mul11 mul22 mul12 mul20 mul01 :
  RationalAlbert → RationalAlbert → O.RationalOctonion

mul00 left right =
  add3O
    (O._*o_ (scalarO (diag1 left)) (scalarO (diag1 right)))
    (O._*o_ (x3 left) (O.octonionConjugate (x3 right)))
    (O._*o_ (O.octonionConjugate (x2 left)) (x2 right))

mul11 left right =
  add3O
    (O._*o_ (O.octonionConjugate (x3 left)) (x3 right))
    (O._*o_ (scalarO (diag2 left)) (scalarO (diag2 right)))
    (O._*o_ (x1 left) (O.octonionConjugate (x1 right)))

mul22 left right =
  add3O
    (O._*o_ (x2 left) (O.octonionConjugate (x2 right)))
    (O._*o_ (O.octonionConjugate (x1 left)) (x1 right))
    (O._*o_ (scalarO (diag3 left)) (scalarO (diag3 right)))

mul12 left right =
  add3O
    (O._*o_ (O.octonionConjugate (x3 left)) (O.octonionConjugate (x2 right)))
    (O._*o_ (scalarO (diag2 left)) (x1 right))
    (O._*o_ (x1 left) (scalarO (diag3 right)))

mul20 left right =
  add3O
    (O._*o_ (x2 left) (scalarO (diag1 right)))
    (O._*o_ (O.octonionConjugate (x1 left)) (O.octonionConjugate (x3 right)))
    (O._*o_ (scalarO (diag3 left)) (x2 right))

mul01 left right =
  add3O
    (O._*o_ (scalarO (diag1 left)) (x3 right))
    (O._*o_ (x3 left) (scalarO (diag2 right)))
    (O._*o_ (O.octonionConjugate (x2 left)) (O.octonionConjugate (x1 right)))

symEntry :
  (RationalAlbert → RationalAlbert → O.RationalOctonion) →
  RationalAlbert → RationalAlbert → O.RationalOctonion
symEntry entry left right =
  halfO (O._+o_ (entry left right) (entry right left))

jordanProduct : RationalAlbert → RationalAlbert → RationalAlbert
jordanProduct left right =
  albert
    (octRealPart (symEntry mul00 left right))
    (octRealPart (symEntry mul11 left right))
    (octRealPart (symEntry mul22 left right))
    (symEntry mul12 left right)
    (symEntry mul20 left right)
    (symEntry mul01 left right)

albertUnit : RationalAlbert
albertUnit = albert 1ℚ 1ℚ 1ℚ O.zeroO O.zeroO O.zeroO

albertTrace : RationalAlbert → ℚ
albertTrace value = diag1 value + diag2 value + diag3 value

------------------------------------------------------------------------
-- Cubic determinant / norm
------------------------------------------------------------------------

doubleReal : O.RationalOctonion → ℚ
doubleReal value =
  octRealPart (O._+o_ value (O.octonionConjugate value))

cubicNorm : RationalAlbert → ℚ
cubicNorm value =
  diag1 value * diag2 value * diag3 value
  - diag1 value * O.octonionNormSq (x1 value)
  - diag2 value * O.octonionNormSq (x2 value)
  - diag3 value * O.octonionNormSq (x3 value)
  + doubleReal (O._*o_ (O._*o_ (x1 value) (x2 value)) (x3 value))

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

record AlbertConstructionBoundary : Set where
  constructor albertConstructionBoundary
  field
    exactRationalOctonionOwnerReused : Bool
    hermitianCarrier27Constructed : Bool
    jordanProductConstructed : Bool
    distinguishedUnitConstructed : Bool
    cubicNormConstructed : Bool
    productMatchesHermitianMatrixSymmetrizationProved : Bool
    unitLawsProved : Bool
    jordanIdentityProved : Bool
    cubicNormJordanCompatibilityProved : Bool
    f4AutomorphismActionConstructed : Bool
    e6CubicNormStabilizerActionConstructed : Bool
    ternary27IntertwinerConstructed : Bool

open AlbertConstructionBoundary public

canonicalAlbertConstructionBoundary : AlbertConstructionBoundary
canonicalAlbertConstructionBoundary =
  albertConstructionBoundary
    true true true true true
    false false false false false false false
