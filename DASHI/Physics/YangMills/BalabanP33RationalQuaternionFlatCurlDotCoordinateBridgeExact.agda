module DASHI.Physics.YangMills.BalabanP33RationalQuaternionFlatCurlDotCoordinateBridgeExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
-- Kenneth G. Wilson, "Confinement of Quarks", Physical Review D 10 (1974),
-- 2445--2459. DOI: 10.1103/PhysRevD.10.2445.
-- Tadeusz Bałaban, "Propagators for Lattice Gauge Theories in a Background
-- Field", Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- This bridge uses only additivity of the already scalar polynomial shape.
-- It never re-opens a twelve-coordinate ring normalization.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (_+_; _*_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.BalabanP33RationalQuaternionFlatCurlScalarExact
open import DASHI.Physics.YangMills.BalabanP33RationalQuaternionFlatCurlPolynomialShapeExact
open import DASHI.Physics.YangMills.BalabanP33RationalQuaternionFlatCurlAtomAssemblyExact
open import DASHI.Physics.YangMills.BalabanP33RationalQuaternionFlatCurlCoordinatesExact

flatRecursionDotExpansionIsCoordinateSum :
  ∀ x0 y0 z0 x1 y1 z1 x2 y2 z2 x3 y3 z3 →
  flatRecursionDotExpansion
    (vec3 x0 y0 z0) (vec3 x1 y1 z1)
    (vec3 x2 y2 z2) (vec3 x3 y3 z3)
  ≡ coordinateRecursionExpansion x0 x1 x2 x3
    + (coordinateRecursionExpansion y0 y1 y2 y3
      + coordinateRecursionExpansion z0 z1 z2 z3)
flatRecursionDotExpansionIsCoordinateSum
    x0 y0 z0 x1 y1 z1 x2 y2 z2 x3 y3 z3 =
  let
    rx = coordinateRecursionExpansion x0 x1 x2 x3
    ry = coordinateRecursionExpansion y0 y1 y2 y3
    rz = coordinateRecursionExpansion z0 z1 z2 z3

    xySplit = flatRecursionShapeAdd
      (x0 * x0) (y0 * y0)
      (x0 * x1) (y0 * y1)
      (x0 * x2) (y0 * y2)
      (x0 * x3) (y0 * y3)
      (x1 * x1) (y1 * y1)
      (x1 * x2) (y1 * y2)
      (x1 * x3) (y1 * y3)
      (x2 * x2) (y2 * y2)
      (x2 * x3) (y2 * y3)
      (x3 * x3) (y3 * y3)

    xyzSplit = flatRecursionShapeAdd
      (x0 * x0 + y0 * y0) (z0 * z0)
      (x0 * x1 + y0 * y1) (z0 * z1)
      (x0 * x2 + y0 * y2) (z0 * z2)
      (x0 * x3 + y0 * y3) (z0 * z3)
      (x1 * x1 + y1 * y1) (z1 * z1)
      (x1 * x2 + y1 * y2) (z1 * z2)
      (x1 * x3 + y1 * y3) (z1 * z3)
      (x2 * x2 + y2 * y2) (z2 * z2)
      (x2 * x3 + y2 * y3) (z2 * z3)
      (x3 * x3 + y3 * y3) (z3 * z3)
  in
  trans xyzSplit
    (trans
      (cong (_+ rz) xySplit)
      (ℚP.+-assoc rx ry rz))

flatOrderedDotExpansionIsCoordinateSum :
  ∀ x0 y0 z0 x1 y1 z1 x2 y2 z2 x3 y3 z3 →
  flatOrderedDotExpansion
    (vec3 x0 y0 z0) (vec3 x1 y1 z1)
    (vec3 x2 y2 z2) (vec3 x3 y3 z3)
  ≡ coordinateRecursionExpansion x0 x1 x2 x3
    + (coordinateRecursionExpansion y0 y1 y2 y3
      + coordinateRecursionExpansion z0 z1 z2 z3)
flatOrderedDotExpansionIsCoordinateSum
    x0 y0 z0 x1 y1 z1 x2 y2 z2 x3 y3 z3 =
  trans
    (sym
      (flatRecursionDotExpansionIsOrdered
        (vec3 x0 y0 z0) (vec3 x1 y1 z1)
        (vec3 x2 y2 z2) (vec3 x3 y3 z3)))
    (flatRecursionDotExpansionIsCoordinateSum
      x0 y0 z0 x1 y1 z1 x2 y2 z2 x3 y3 z3)

flatDisplayedOrderedExpansionIsCoordinateSum :
  ∀ x0 y0 z0 x1 y1 z1 x2 y2 z2 x3 y3 z3 →
  flatDisplayedOrderedExpansion
    (vec3 x0 y0 z0) (vec3 x1 y1 z1)
    (vec3 x2 y2 z2) (vec3 x3 y3 z3)
  ≡ coordinateRecursionExpansion x0 x1 x2 x3
    + (coordinateRecursionExpansion y0 y1 y2 y3
      + coordinateRecursionExpansion z0 z1 z2 z3)
flatDisplayedOrderedExpansionIsCoordinateSum
    x0 y0 z0 x1 y1 z1 x2 y2 z2 x3 y3 z3 =
  trans
    (sym
      (flatOrderedDotExpansionIsDisplayed
        (vec3 x0 y0 z0) (vec3 x1 y1 z1)
        (vec3 x2 y2 z2) (vec3 x3 y3 z3)))
    (flatOrderedDotExpansionIsCoordinateSum
      x0 y0 z0 x1 y1 z1 x2 y2 z2 x3 y3 z3)
