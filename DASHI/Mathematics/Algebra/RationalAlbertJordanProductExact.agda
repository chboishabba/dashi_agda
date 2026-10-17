module DASHI.Mathematics.Algebra.RationalAlbertJordanProductExact where

------------------------------------------------------------------------
-- RATIONAL ALBERT JORDAN PRODUCT
--
-- Builds on `RationalAlbertHermitianCubicExact` and the existing exact rational
-- octonions.  For the Hermitian coordinate convention
--
--       [ a       z       conjugate(y) ]
--       [ conjugate(z) b  x            ]
--       [ y       conjugate(x) c       ]
--
-- this file writes the coordinates of (XY + YX)/2 directly.  Because the
-- ambient octonion matrix product is not associative, the exceptional Jordan
-- identity is a separate theorem obligation and is not inferred from generic
-- associative-matrix machinery.
--
-- A companion local Python exact-rational probe checks unit, commutativity and
-- the Jordan identity on randomized coordinate inputs.  That diagnostic is not
-- promoted here as Agda kernel authority.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; ½; _+_; _*_; -_)

import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Mathematics.Algebra.CayleyDicksonRationalOctonionExact as O
import DASHI.Mathematics.Algebra.RationalAlbertHermitianCubicExact as A

------------------------------------------------------------------------
-- Octonion linear helpers.
------------------------------------------------------------------------

innerO : O.RationalOctonion → O.RationalOctonion → ℚ
innerO left right =
  A.realPartO (O._*o_ left (O.octonionConjugate right))

halfO : O.RationalOctonion → O.RationalOctonion
halfO value = A.scaleO ½ value

sumO2 : O.RationalOctonion → O.RationalOctonion → O.RationalOctonion
sumO2 = O._+o_

sumO6 :
  O.RationalOctonion → O.RationalOctonion → O.RationalOctonion →
  O.RationalOctonion → O.RationalOctonion → O.RationalOctonion →
  O.RationalOctonion
sumO6 a b c d e f =
  O._+o_ (O._+o_ (O._+o_ a b) (O._+o_ c d)) (O._+o_ e f)

------------------------------------------------------------------------
-- Coordinate Jordan product.
------------------------------------------------------------------------

jordanProduct : A.RationalAlbert → A.RationalAlbert → A.RationalAlbert
jordanProduct
  (A.albert a b c x y z)
  (A.albert a' b' c' x' y' z') =
  A.albert d0 d1 d2 ox oy oz
  where
    d0 : ℚ
    d0 = a * a' + innerO z z' + innerO y y'

    d1 : ℚ
    d1 = b * b' + innerO z z' + innerO x x'

    d2 : ℚ
    d2 = c * c' + innerO y y' + innerO x x'

    ox : O.RationalOctonion
    ox = halfO
      (sumO6
        (O._*o_ (O.octonionConjugate z) (O.octonionConjugate y'))
        (A.scaleO b x')
        (A.scaleO c' x)
        (O._*o_ (O.octonionConjugate z') (O.octonionConjugate y))
        (A.scaleO b' x)
        (A.scaleO c x'))

    oy : O.RationalOctonion
    oy = halfO
      (sumO6
        (A.scaleO a' y)
        (O._*o_ (O.octonionConjugate x) (O.octonionConjugate z'))
        (A.scaleO c y')
        (A.scaleO a y')
        (O._*o_ (O.octonionConjugate x') (O.octonionConjugate z))
        (A.scaleO c' y))

    oz : O.RationalOctonion
    oz = halfO
      (sumO6
        (A.scaleO a z')
        (A.scaleO b' z)
        (O._*o_ (O.octonionConjugate y) (O.octonionConjugate x'))
        (A.scaleO a' z)
        (A.scaleO b z')
        (O._*o_ (O.octonionConjugate y') (O.octonionConjugate x)))

squareA : A.RationalAlbert → A.RationalAlbert
squareA value = jordanProduct value value

------------------------------------------------------------------------
-- Exact theorem targets.  These are now algebraic identities on an actual
-- product, rather than placeholders over a 27-point set.
------------------------------------------------------------------------

data ProductCommutativityPaid : Set where
data UnitLawsPaid : Set where
data JordanIdentityPaid : Set where

JordanIdentity : Set
JordanIdentity =
  (x y : A.RationalAlbert) →
    jordanProduct (jordanProduct (squareA x) y) x
    ≡ jordanProduct (squareA x) (jordanProduct y x)

record AlbertProductFrontier : Set where
  constructor albert-product-frontier
  field
    productFormulaSourceWritten : Bool
    carrierIsRationalHermitian27 : Bool
    unitCandidateIsDiagonalIdentity : Bool
    cubicNormAlreadySourceWritten : Bool
    localExactRationalUnitTestsPass : Bool
    localExactRationalCommutativityTestsPass : Bool
    localExactRationalJordanIdentityTestsPass : Bool
    agdaProductCommutativityPaid : Bool
    agdaUnitLawsPaid : Bool
    agdaJordanIdentityPaid : Bool
    f4AutomorphismActionPaid : Bool
open AlbertProductFrontier public

currentAlbertProductFrontier : AlbertProductFrontier
currentAlbertProductFrontier =
  albert-product-frontier
    true true true true
    true true true
    false false false false
