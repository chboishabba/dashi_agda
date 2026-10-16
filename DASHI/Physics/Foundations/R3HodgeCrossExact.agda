module DASHI.Physics.Foundations.R3HodgeCrossExact where

------------------------------------------------------------------------
-- EXPLICIT 3D WEDGE / HODGE / CROSS IDENTIFICATION
--
-- The repository already owns the continuous three-coordinate su(2) carrier
-- and its Euclidean minors.  This module packages those minors as the three
-- coordinates of Lambda^2(R^3), applies the oriented 3D Hodge map, and proves
-- that the result is exactly the usual cross-product coordinate vector.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier as R
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as V3
import DASHI.Physics.YangMills.BalabanSU2LieBracket as Lie
import DASHI.Physics.YangMills.BalabanP33SU2EuclideanGeometryExact as Euclidean

record Bivector3 : Set where
  constructor bivector3
  field
    xy yz zx : R.ℝ

open Bivector3 public

wedge3 : V3.SU2LieAlgebra → V3.SU2LieAlgebra → Bivector3
wedge3 u v =
  bivector3
    (Euclidean.minorXY u v)
    (Euclidean.minorYZ u v)
    ((V3.zComponent u R.*R V3.xComponent v)
      R.+R (R.-R (V3.xComponent u R.*R V3.zComponent v)))

hodgeStar3 : Bivector3 → V3.SU2LieAlgebra
hodgeStar3 omega =
  V3.su2Lie (yz omega) (zx omega) (xy omega)

cross3 : V3.SU2LieAlgebra → V3.SU2LieAlgebra → V3.SU2LieAlgebra
cross3 u v =
  V3.su2Lie
    (Euclidean.minorYZ u v)
    ((V3.zComponent u R.*R V3.xComponent v)
      R.+R (R.-R (V3.xComponent u R.*R V3.zComponent v)))
    (Euclidean.minorXY u v)

hodgeWedgeEqualsCross : ∀ u v →
  hodgeStar3 (wedge3 u v) ≡ cross3 u v
hodgeWedgeEqualsCross u v = refl

crossSwapNegates : ∀ u v →
  cross3 v u ≡ V3.lieNegate (cross3 u v)
crossSwapNegates
  (V3.su2Lie x1 y1 z1) (V3.su2Lie x2 y2 z2) =
  V3.su2LieExt
    (Lie.anti1 x1 y1 z1 x2 y2 z2)
    (Lie.anti2 x1 y1 z1 x2 y2 z2)
    (Lie.anti3 x1 y1 z1 x2 y2 z2)

-- Repository normalization: the literal su(2) commutator is twice this cross.
lieBracketIsTwoCross : ∀ u v →
  Lie.lieBracket u v ≡ V3.lieScale Lie.twoR (cross3 u v)
lieBracketIsTwoCross
  (V3.su2Lie x1 y1 z1) (V3.su2Lie x2 y2 z2) = refl

r3HodgeWedgeCrossClosed : Bool
r3HodgeWedgeCrossClosed = true

reusesExistingSU2EuclideanMinors : Bool
reusesExistingSU2EuclideanMinors = true

hodgeOrientationMatchesRightHandCross : Bool
hodgeOrientationMatchesRightHandCross = true

specificR3BivectorHodgeTheoremPaid : Bool
specificR3BivectorHodgeTheoremPaid = true

record R3HodgeCrossBoundary : Set where
  constructor r3-hodge-cross-boundary
  field
    explicitBivectorCoordinatesConstructed : Bool
    hodgeMapConstructed : Bool
    hodgeWedgeEqualsCrossProved : Bool
    su2BracketNormalizationConnected : Bool
    genericHigherDimensionalHodgeTheoryClaimed : Bool

canonicalR3HodgeCrossBoundary : R3HodgeCrossBoundary
canonicalR3HodgeCrossBoundary =
  r3-hodge-cross-boundary true true true true false
