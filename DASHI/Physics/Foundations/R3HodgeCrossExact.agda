module DASHI.Physics.Foundations.R3HodgeCrossExact where

------------------------------------------------------------------------
-- EXPLICIT 3D WEDGE / HODGE / CROSS IDENTIFICATION
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import Data.List.Base using ([]; _∷_)
import Tactic.RingSolver as Solver

open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  ( _+R_; _*R_; -R_; realSolverRing )
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as V3
import DASHI.Physics.YangMills.BalabanSU2LieBracket as Lie
import DASHI.Physics.YangMills.BalabanP33SU2EuclideanGeometryExact as Euclidean

record Bivector3 : Set where
  constructor bivector3
  field
    xy yz zx : ℝ

open Bivector3 public

wedge3 : V3.SU2LieAlgebra → V3.SU2LieAlgebra → Bivector3
wedge3 u v =
  bivector3
    (Euclidean.minorXY u v)
    (Euclidean.minorYZ u v)
    ((V3.zComponent u *R V3.xComponent v)
      +R (-R (V3.xComponent u *R V3.zComponent v)))

hodgeStar3 : Bivector3 → V3.SU2LieAlgebra
hodgeStar3 omega =
  V3.su2Lie (yz omega) (zx omega) (xy omega)

cross3 : V3.SU2LieAlgebra → V3.SU2LieAlgebra → V3.SU2LieAlgebra
cross3 u v =
  V3.su2Lie
    (Euclidean.minorYZ u v)
    ((V3.zComponent u *R V3.xComponent v)
      +R (-R (V3.xComponent u *R V3.zComponent v)))
    (Euclidean.minorXY u v)

hodgeWedgeEqualsCross : ∀ u v →
  hodgeStar3 (wedge3 u v) ≡ cross3 u v
hodgeWedgeEqualsCross u v = refl

crossSwapNegates : ∀ u v →
  cross3 v u ≡ V3.lieNegate (cross3 u v)
crossSwapNegates
  (V3.su2Lie x1 y1 z1) (V3.su2Lie x2 y2 z2) =
  V3.su2LieExt
    (Solver.solve (x1 ∷ y1 ∷ z1 ∷ x2 ∷ y2 ∷ z2 ∷ []) realSolverRing)
    (Solver.solve (x1 ∷ y1 ∷ z1 ∷ x2 ∷ y2 ∷ z2 ∷ []) realSolverRing)
    (Solver.solve (x1 ∷ y1 ∷ z1 ∷ x2 ∷ y2 ∷ z2 ∷ []) realSolverRing)

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
    crossAntisymmetryProved : Bool
    su2BracketNormalizationConnected : Bool
    genericHigherDimensionalHodgeTheoryClaimed : Bool

canonicalR3HodgeCrossBoundary : R3HodgeCrossBoundary
canonicalR3HodgeCrossBoundary =
  r3-hodge-cross-boundary true true true true true false
